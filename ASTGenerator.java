import java.io.File;
import java.io.IOException;

import java.util.ArrayList;
import java.util.Arrays;
import java.nio.charset.Charset;
import java.nio.file.Files;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;
import org.antlr.v4.runtime.Token;

public class ASTGenerator {

    static ArrayList<String> ClassTag = new ArrayList<String>();
    static ArrayList<String> LineNum = new ArrayList<String>();
    static ArrayList<String> Type = new ArrayList<String>();
    static ArrayList<String> Content = new ArrayList<String>();
    static ArrayList<Integer> CodeLine = new ArrayList<Integer>();
    static ArrayList<Integer> CharPos = new ArrayList<Integer>();

    static ArrayList<String> terminalNodes = new ArrayList<String>();
    static ArrayList<String> terminalLineNum = new ArrayList<String>();
    static ParserRuleContext mctx;
    static String classTagName;
    static String projectNameTag;

    static ArrayList<ParserRuleContext> masterCtx = new ArrayList<ParserRuleContext>();
    static ArrayList<ArrayList[]> masterMemory = new ArrayList<ArrayList[]>();
    static ArrayList[] baseClassArray = new ArrayList[5];

    private static String readFile(String filepath) throws IOException {
        File file = new File(filepath);
        byte[] encoded = Files.readAllBytes(file.toPath());
        return new String(encoded, Charset.forName("UTF-8"));
    }

    public static void main(String args[]) throws IOException{

        String[] filepaths = {"/Users/anjandash/Desktop/ASTBaseFilesEX/testers/CallGraphs.java", "/Users/anjandash/Desktop/ASTBaseFilesEX/testers/GetValue.java"};
        
        projectNameTag = "10000";
        classTagName = "1000";


        System.out.println("digraph G {");

            for(int i=0; i<filepaths.length; i++){

                String filepath = filepaths[i];

                LineNum = new ArrayList<String>();
                Type = new ArrayList<String>();
                Content = new ArrayList<String>();
                CodeLine = new ArrayList<Integer>();
                CharPos = new ArrayList<Integer>();
                terminalNodes = new ArrayList<String>();
                terminalLineNum = new ArrayList<String>();
            
                String inputString = readFile(filepath);
                ANTLRInputStream input = new ANTLRInputStream(inputString);
                Java8Lexer lexer = new Java8Lexer(input);
                CommonTokenStream tokens = new CommonTokenStream(lexer);
                Java8Parser parser = new Java8Parser(tokens);
                ParserRuleContext ctx = parser.compilationUnit();

                String classTagValue = "x";
                generateAST(ctx, false, 0, classTagValue);
                mctx = ctx;

                baseClassArray[0] = LineNum;
                baseClassArray[1] = Type;
                baseClassArray[2] = Content;
                baseClassArray[3] = CodeLine;
                baseClassArray[4] = CharPos;

                masterMemory.add(baseClassArray);
                masterCtx.add(mctx);

                // ########################

                printDOT();
                // printNextTokensGraph();
                // printGuardedBy();
                // printComputedFrom();
                // printLastLexicalUse();


                // ########################  



                int tmp = Integer.parseInt(classTagName) + 1;
                classTagName = Integer.toString(tmp);
            }

            //printDOT();
            //printReturnsTo();
            //printFormalArgs();

        System.out.println("}");

    }

    // @@@@@@@@@@@@@@@@@@@@@@@@

    private static void printReturnsTo(){

        String classlabel = "";
        String classrule = "";
        String classcontent = "";
        String classline = "";
        String classcharpos = "";
        
        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            String mname;
            ArrayList<String> arguments = new ArrayList<String>();
            ArrayList<String> RTStrings = new ArrayList<String>();
            ArrayList<String> RTLabels = new ArrayList<String>();

            if(localrule.startsWith("normalClassDeclaration")){
                classlabel = locallabel;
                classrule = localrule;
                classcontent = localcontent;
                classline = localline;
                classcharpos = localcharpos;
            }

            if(localrule.startsWith("methodInvocation")){
                if(localrule.equals("methodInvocation_lfno_primary")){

                    RuleContext targetctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                    mname = getMethodNameFromctx(targetctx);
                    arguments = getExpNames(targetctx);

                    //System.out.println("Method Name found:" + mname);
                    //System.out.println("Arguments found:");
                    for(int k=0; k<arguments.size(); k++){
                        //System.out.println(arguments.get(k));
                    }

                    //pass the class ctx and find the label of the target method name

                    RuleContext classctx = getctxForCombination(mctx, classlabel, classrule, classcontent, classline, classcharpos);
                    String RTmethodlbl = getLabelsForMethodDeclaratorS(classctx, mname);

                    RuleContext rctx = getParentMethodDecl(RTmethodlbl);
                    RTStrings = getReturnStatements(rctx);

                    for(int l=0; l<RTStrings.size(); l++){

                        ArrayList<String> iniRTLabels = new ArrayList<String>();
                        iniRTLabels = getRetLabels(rctx, RTStrings.get(l));

                        for(int m=0; m<iniRTLabels.size(); m++){
                            RTLabels.add(iniRTLabels.get(m));
                        }
                    }

                    // We have all Return Labels in RTLabels
                    // We have the current methodInvocation_lfno_primary as locallabel
                    // Connect from RetLabels to locallabel

                    for(int m=0; m<RTLabels.size(); m++){
                        System.out.println(RTLabels.get(m)+"->"+locallabel + " [label=\"RT\", color=\"lime\"]");
                    }

                } else if(localrule.equals("methodInvocation_lf_primary")){

                    // find class name
                    // find method name
                    // look for class name
                    // look for the method name

                    // get ctx and get the details



                }

            }

        }

    }

    private static void printFormalArgs(){

        String classlabel = "";
        String classrule = "";
        String classcontent = "";
        String classline = "";
        String classcharpos = "";
        
        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            String mname;
            ArrayList<String> arguments = new ArrayList<String>();
            ArrayList<String> RTStrings = new ArrayList<String>();
            ArrayList<String> RTLabels = new ArrayList<String>();

            if(localrule.startsWith("normalClassDeclaration")){
                classlabel = locallabel;
                classrule = localrule;
                classcontent = localcontent;
                classline = localline;
                classcharpos = localcharpos;
            }

            if(localrule.startsWith("methodInvocation")){
                if(localrule.equals("methodInvocation_lfno_primary")){

                    RuleContext targetctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                    mname = getMethodNameFromctx(targetctx);
                    arguments = getExpNames(targetctx);


                    //pass the class ctx and find the label of the target method name
                    RuleContext classctx = getctxForCombination(mctx, classlabel, classrule, classcontent, classline, classcharpos);

                    if(!classctx.equals(mctx) && !classctx.equals(null)){

                        ArrayList<String> RTmethodlbls = getLabelsForMethodDeclarator(classctx, mname);
                        String RTmethodlbl = "";

            
                        if(RTmethodlbls.size() == 1){
                            RTmethodlbl = RTmethodlbls.get(0);
                            RuleContext rctx = getParentMethodDecl(RTmethodlbl);


                            if(!rctx.equals(mctx) && !rctx.equals(null)){

                                // Now, we have arguments in arguments variable
                                // For each expressionName in arguments 
                                // we search in the methodDeclarator for all variableDeclaratorId (and get its label)
                                // Then connect the two

                                RuleContext xctx = getctxForLabel(RTmethodlbl);
                                

                                if(!xctx.equals(mctx) && !xctx.equals(null)){

                                    ArrayList<String> varids = getExpNamesByDeclaration(xctx);

                                    if(arguments.size() == varids.size()){

                                        for(int j=0; j<arguments.size(); j++){
                                            ArrayList<String> falabel = getExpLabels(targetctx, arguments.get(j));
                                            ArrayList<String> farglabel = getVDILabels(xctx, varids.get(j));

                                            if(falabel.size() == 1 && farglabel.size() == 1){
                                                
                                                System.out.println(falabel.get(0)+"->"+farglabel.get(0) + " [label=\"FA\", color=\"pink\"]"); 

                                            } else {
                                                System.out.println("For context: "+ xctx.getText());
                                                System.out.println("Unexpected number of labels found for: " + arguments.get(j) + " No. of calling instances: "+ falabel.size() +" Matching arg: "+ varids.get(j) +" called instances: "+ farglabel.size());
                                            }
                                        }

                                    } else { System.out.println("ERR: Number of arguments does not match number of parameters for " + RTmethodlbl); }
                                } else { System.out.println("ERR: Context not found for " + RTmethodlbl); }
                            } else { System.out.print("ERR: Parent Ctx not found for "+ RTmethodlbl); }
                        } else { System.out.println("ERR: Unexpected size of Labels found for method: "+ mname + " Size: " + RTmethodlbls.size()); }
                    } else { System.out.println("ERR: Class Ctx not found for "+ targetctx.getText()); }
                } else if(localrule.equals("methodInvocation")){



                }

            }

        }

    }

    private static RuleContext getParentMethodDecl(String RTmethodlbl){

        RuleContext rctx = mctx;

        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if(localrule.startsWith("methodDeclaration")){
                String mlabel = locallabel;
                String mrule = localrule;
                String mcontent = localcontent;
                String mline = localline;
                String mcharpos = localcharpos;
            }

            if(locallabel.equals(RTmethodlbl)){

                rctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                return rctx;
            }

        }

        return rctx;

    }

    private static RuleContext getctxForLabel(String RTmethodlbl){

        RuleContext rctx = mctx;

        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if(locallabel.equals(RTmethodlbl)){
                rctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                return rctx;
            }
        }

        return rctx;

    }

    // @@@@@@@@@@@@@@@@@@@@@@@@

    private static void generateAST(RuleContext ctx, boolean verbose, int indentation, String classTagValue) {
        boolean toBeIgnored = !verbose && ctx.getChildCount() == 1 && ctx.getChild(0) instanceof ParserRuleContext;
        ParserRuleContext r = (ParserRuleContext) ctx;

        if (!toBeIgnored) {
            String ruleName = Java8Parser.ruleNames[ctx.getRuleIndex()];
            //ClassTag.add(classTagValue);
            LineNum.add(Integer.toString(indentation));
            Type.add(ruleName);
            Content.add(ctx.getText());
            CodeLine.add(r.getStart().getLine());
            CharPos.add(r.getStart().getCharPositionInLine());
        }
        
        for (int i = 0; i < ctx.getChildCount(); i++) {
            ParseTree element = ctx.getChild(i);
            if (element instanceof RuleContext) {
                generateAST((RuleContext) element, verbose, indentation + (toBeIgnored ? 0 : 1), classTagValue);
            } else if (element instanceof TerminalNode){
                if(!(element.getText()).equals("<EOF>")){
                    //ClassTag.add(classTagValue);
                    LineNum.add(Integer.toString(indentation+1));
                    Type.add("terminalNode");
                    Content.add(element.getText());
                    CodeLine.add( ((Token) element.getPayload()).getLine() );
                    CharPos.add(  ((Token) element.getPayload()).getCharPositionInLine() );

                    terminalNodes.add(element.getText());
                }
            }
        }
    }

    private static void printDOT(){
        printLabel();
        int pos = 0;
        for(int i=1; i<LineNum.size();i++){
            pos=getPos(Integer.parseInt(LineNum.get(i))-1, i);
            System.out.println( classTagName+((Integer.parseInt(LineNum.get(i))-1)+Integer.toString(pos))+"->"+ classTagName+(LineNum.get(i)+i) + " [label=\"child\"]");
        }
    }

    private static void printNextTokensGraph(){
        String label;
        String rule;
        String content;
        String line;

        for(int i=0; i<LineNum.size(); i++){

            label = LineNum.get(i)+i;
            rule = Type.get(i);
            content = Content.get(i);
            line = Integer.toString(CodeLine.get(i));

            if(terminalNodes.size() > 0){
                if(content.equals(terminalNodes.get(0)) && rule.equals("terminalNode")){
                    terminalNodes.remove(0);
                    terminalLineNum.add(label);
                }
            }
        }

        for(int k=0; k<(terminalLineNum.size()-1); k++){
            System.out.println( classTagName+terminalLineNum.get(k)+"->"+classTagName+terminalLineNum.get(k+1) + " [label=\"NT\", arrowhead=\"box\", color=\"red\"]");
        }
    }

    // ########################

    private static void printGuardedBy(){
        String label;
        String rule;
        String content;
        String line;
        String charpos;

        String parentlabel;
        String parentrule;
        String parentcontent;
        String parentline;
        String parentcharpos;

        ArrayList<String> expNames = new ArrayList<String>();
        RuleContext parentrctx = mctx; 
        RuleContext rctx;
        boolean guardedBy;
        boolean parentVisited = false;

        for(int i=0; i<LineNum.size(); i++){
            
            label = LineNum.get(i)+i;
            rule = Type.get(i);
            content = Content.get(i);
            line = Integer.toString(CodeLine.get(i));
            charpos = Integer.toString(CharPos.get(i));

            if(rule.equals("ifThenElseStatement")){
                parentlabel = LineNum.get(i)+i;
                parentrule = Type.get(i);
                parentcontent = Content.get(i);
                parentline = Integer.toString(CodeLine.get(i));
                parentcharpos = Integer.toString(CharPos.get(i));

                parentrctx = getctxForCombination(mctx, parentlabel, parentrule, parentcontent, parentline, parentcharpos);
                if(parentrctx.equals(mctx) || parentrctx.equals(null)){
                    System.out.println("ERROR: ctx for ifThenElseStatement not found");
                }
                parentVisited = true;
            }

            if(parentVisited){
                guardHandler(parentrctx);
                parentVisited = false;
            }

        }
    }

    private static void guardHandler(RuleContext parentrctx){

        String lbl = getlabelForContext(parentrctx);
        int counter = 0;
        boolean started = false;
        ArrayList<String> expNames = new ArrayList<String>();

        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if(lbl.equals(locallabel)){
                started = true;
                continue;
            }

            if(started){
                if(!localrule.equals("block")){
                    if(localrule.equals("relationalExpression")){
                        // collect all target expressionName(s) in the relationalExpression in an ArrayList
                        // send the parseTree to a function which will return the ArrayList of all expressionName(s) in it

                        RuleContext rctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                        if(rctx.equals(mctx)){System.out.println("ERROR: ctx for relationalExpression not found");}

                        expNames = getExpNames(rctx);

                        for(int j=0; j<parentrctx.getChildCount(); j++){
                            ParseTree element = parentrctx.getChild(j);
                            
                            if(element instanceof RuleContext){
                                RuleContext localctx = (RuleContext) element;

                                //GuardedBy
                                if("statementNoShortIf".equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                                    RuleContext localblockctx = localctx;

                                    for(int k=0; k<expNames.size(); k++){
                                        String localexpName = expNames.get(k);

                                        // traverse localblockctx and find expressionName which matched localexpName
                                        // collect the label for every matching expressionName

                                        ArrayList<String> startLabels = getExpLabels(localblockctx, localexpName);
                                        String targetLabel = getlabelForContext(rctx);

                                        if(targetLabel.equals("NF")){
                                            System.out.println("ERROR: label for relationalExpression not found");
                                        } else {
                                            for(int l=0; l<startLabels.size(); l++){
                                                String start = startLabels.get(l);

                                                System.out.println(classTagName+start+"->"+classTagName+targetLabel + " [label=\"GB\", color=\"blue\"]");
                                            }
                                        }
                                    }
                                }

                                //GuardedByNegation
                                if("statement".equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                                    RuleContext localblockctx = localctx;

                                    for(int k=0; k<expNames.size(); k++){
                                        String localexpName = expNames.get(k);

                                        // traverse localblockctx and find expressionName which matched localexpName
                                        // collect the label for every matching expressionName

                                        ArrayList<String> startLabels = getExpLabels(localblockctx, localexpName);
                                        String targetLabel = getlabelForContext(rctx);

                                        if(targetLabel.equals("NF")){
                                            System.out.println("ERROR: label for relationalExpression not found");
                                        } else {
                                            for(int l=0; l<startLabels.size(); l++){
                                                String start = startLabels.get(l);

                                                System.out.println(classTagName+start+"->"+classTagName+targetLabel + " [label=\"GBN\", color=\"red\"]");
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        
                    }


                } else {
                    break;
                }
                
                counter++;

            }

        }

    }

    private static RuleContext getctxForCombination(RuleContext ctx, String label, String rule, String content, String line, String charpos){

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()]) && content.equals(localctx.getText()) && line.equals(Integer.toString(((ParserRuleContext) localctx).getStart().getLine())) && charpos.equals(Integer.toString(((ParserRuleContext) localctx).getStart().getCharPositionInLine())) ){
                    return localctx;                    
                } else {
                    RuleContext returnctx = getctxForCombination(localctx, label, rule, content, line, charpos);
                    if(!returnctx.equals(mctx) && !returnctx.equals(null)){
                            return returnctx;
                    }
                }
            } else if (element instanceof TerminalNode){
                continue;
            }
        }
        return mctx;
    }

    private static String getlabelForContext(RuleContext ctx){     
        String rule;
        String content;
        String line;
        String charpos;

        rule = Java8Parser.ruleNames[ctx.getRuleIndex()];
        content = ctx.getText();
        line = Integer.toString(((ParserRuleContext) ctx).getStart().getLine());
        charpos = Integer.toString(((ParserRuleContext) ctx).getStart().getCharPositionInLine());

        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if(localrule.equals(rule) && localcontent.equals(content) && localline.equals(line) && localcharpos.equals(charpos)){
                return locallabel;
            }
        }
        return "NF";
    }

    private static ArrayList getExpNames(RuleContext ctx){
        String rule = "expressionName";
        ArrayList<String> expNames = new ArrayList<String>();
        ArrayList<String> expNamesRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    expNames.add(localctx.getText());
                } else {
                    expNamesRET = getExpNames(localctx);
                    for(int j=0; j<expNamesRET.size(); j++){
                        expNames.add(expNamesRET.get(j));
                    }
                }
            }
        }

        return expNames;
    }

    private static ArrayList getReturnStatements(RuleContext ctx){
        String rule = "returnStatement";
        ArrayList<String> retStmts = new ArrayList<String>();
        ArrayList<String> retStmtsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    retStmts.add(localctx.getText());
                } else {
                    retStmtsRET = getReturnStatements(localctx);
                    for(int j=0; j<retStmtsRET.size(); j++){
                        retStmts.add(retStmtsRET.get(j));
                    }
                }
            }
        }

        return retStmts;
    }


    private static String getMethodNameFromctx(RuleContext ctx){
        String rule = "methodName";
        String mname = "";

        for(int i=0; i<ctx.getChildCount(); i++){

            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    return (localctx.getText());
                } 
            }

        }

        return mname;
    }

    private static ArrayList getExpNamesByDeclaration(RuleContext ctx){
        String rule = "variableDeclaratorId";
        ArrayList<String> expNames = new ArrayList<String>();
        ArrayList<String> expNamesRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    expNames.add(localctx.getText());
                } else {
                    expNamesRET = getExpNamesByDeclaration(localctx);
                    for(int j=0; j<expNamesRET.size(); j++){
                        expNames.add(expNamesRET.get(j));
                    }
                }
            }
        }

        return expNames;
    }

    private static ArrayList getExpLabels(RuleContext ctx, String expName){
        String rule = "expressionName";
        ArrayList<String> expLabels = new ArrayList<String>();
        ArrayList<String> expLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    if(expName.equals(localctx.getText())){
                        String rc = getlabelForContext(localctx);
                        if(!rc.equals("NF")){
                            expLabels.add(rc);
                        }    
                    }
                } else {
                    expLabelsRET = getExpLabels(localctx, expName);
                    for(int j=0; j<expLabelsRET.size(); j++){
                        expLabels.add(expLabelsRET.get(j));
                    }
                }
            }
        }

        return expLabels;
    }

    private static ArrayList getVDILabels(RuleContext ctx, String VDIName){
        String rule = "variableDeclaratorId";
        ArrayList<String> vdiLabels = new ArrayList<String>();
        ArrayList<String> vdiLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    if(VDIName.equals(localctx.getText())){
                        String rc = getlabelForContext(localctx);
                        if(!rc.equals("NF")){
                            vdiLabels.add(rc);
                        }    
                    }
                } else {
                    vdiLabelsRET = getVDILabels(localctx, VDIName);
                    for(int j=0; j<vdiLabelsRET.size(); j++){
                        vdiLabels.add(vdiLabelsRET.get(j));
                    }
                }
            }
        }

        return vdiLabels;
    }

    private static ArrayList getRetLabels(RuleContext ctx, String retContent){
        String rule = "returnStatement";
        ArrayList<String> retLabels = new ArrayList<String>();
        ArrayList<String> retLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    if(retContent.equals(localctx.getText())){
                        String rc = getlabelForContext(localctx);
                        if(!rc.equals("NF")){
                            retLabels.add(rc);
                        }    
                    }
                } else {
                    retLabelsRET = getRetLabels(localctx, retContent);
                    for(int j=0; j<retLabelsRET.size(); j++){
                        retLabels.add(retLabelsRET.get(j));
                    }
                }
            }
        }

        return retLabels;
    }



    private static String getLabelsForMethodDeclaratorS(RuleContext ctx, String methodName){
        String rule = "methodDeclarator";
        String mLabel = "";

        ArrayList<String> expLabels = new ArrayList<String>();
        ArrayList<String> expLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;



                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){

                    String[] parts = localctx.getText().split("\\(", 2);



                    boolean contains = Arrays.stream(parts).anyMatch(methodName::equals);

                    if(contains){
                        mLabel = getlabelForContext(localctx);
                        return mLabel;
                    }

                } else {
                    mLabel = getLabelsForMethodDeclaratorS(localctx, methodName);
                }
            }
        }

        return mLabel;
    }

    private static ArrayList getExpLabelsByDecl(RuleContext ctx, String expName){
        String rule = "variableDeclaratorId";
        ArrayList<String> expLabels = new ArrayList<String>();
        ArrayList<String> expLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){
                    if(expName.equals(localctx.getText())){
                        String rc = getlabelForContext(localctx);
                        if(!rc.equals("NF")){
                            expLabels.add(rc);
                        }    
                    }
                } else {
                    expLabelsRET = getExpLabelsByDecl(localctx, expName);
                    for(int j=0; j<expLabelsRET.size(); j++){
                        expLabels.add(expLabelsRET.get(j));
                    }
                }
            }
        }

        return expLabels;
    }

    private static ArrayList getLabelsForMethodDeclarator(RuleContext ctx, String mName){
        String rule = "methodDeclarator";
        ArrayList<String> mLabels = new ArrayList<String>();
        ArrayList<String> mLabelsRET = new ArrayList<String>();

        for(int i=0; i<ctx.getChildCount(); i++){
            ParseTree element = ctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext localctx = (RuleContext) element;
                if(rule.equals(Java8Parser.ruleNames[localctx.getRuleIndex()])){


                    String[] parts = localctx.getText().split("\\(", 2);
                    boolean contains = Arrays.stream(parts).anyMatch(mName::equals);

                    if(contains){
                        String rc = getlabelForContext(localctx);
                        if(!rc.equals("NF")){
                            mLabels.add(rc);
                        }    
                    }


                } else {
                    mLabelsRET = getLabelsForMethodDeclarator(localctx, mName);
                    for(int j=0; j<mLabelsRET.size(); j++){
                        mLabels.add(mLabelsRET.get(j));
                    }
                }
            }
        }

        return mLabels;
    }


    // ************************

    private static void printComputedFrom(){

        //System.out.println("printCom1");
        
        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if("assignment".equals(localrule)){

                //System.out.println("printCom2");

                // get the first child label as source
                RuleContext assignctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                computedHandler(assignctx);

                // send the ctx after assignmentOperator to retrieve labels of other existing expressionNames
            }

        }
    }

    private static void computedHandler(RuleContext assignctx){

        //System.out.println("printCom3");

        boolean assignVisited = false;
        ArrayList<String> dstNames = new ArrayList<String>();
        ArrayList<String> dstNamesWD = new ArrayList<String>();
        ArrayList<String> dstLabels = new ArrayList<String>();
        ArrayList<String> dstLabelsList = new ArrayList<String>();
        ArrayList<String> srcLabels = new ArrayList<String>();
        String srcLabel = "";

        for(int i=0; i<assignctx.getChildCount(); i++){
            ParseTree element = assignctx.getChild(i);
            if(element instanceof RuleContext){
                RuleContext lctx = (RuleContext) element;

                if(!assignVisited){
                     //System.out.println("printCom4");
                     //System.out.println(Java8Parser.ruleNames[lctx.getRuleIndex()]);
                    if("leftHandSide".equals( Java8Parser.ruleNames[lctx.getRuleIndex()] )){
                        srcLabels = getExpLabels(lctx, lctx.getText());

                        // for(int m=0; m<srcLabels.size(); m++){
                        //     System.out.println(srcLabels.get(m));
                        // }

                        if(srcLabels.size() == 1){
                            srcLabel = srcLabels.get(0);
                        }
                        
                    } else if ("assignmentOperator".equals(Java8Parser.ruleNames[lctx.getRuleIndex()])){
                        assignVisited = true;
                        continue;
                    }
                }

                if(assignVisited){
                    dstNamesWD = getExpNames(lctx);
                    dstNames = removeDuplicates(dstNamesWD);


                    for(int j=0; j<dstNames.size(); j++){
                        //System.out.println("-----------------");
                        //System.out.println("dst Name #"+j+" >> " + dstNames.get(j));

                        dstLabelsList = getExpLabels(lctx, dstNames.get(j));
                        for(int k=0; k<dstLabelsList.size(); k++){
                            dstLabels.add(dstLabelsList.get(k));
                        }
                    }
                    break;
                }
                
            }
        }

        // print src to dst links
        for(int k=0; k<dstLabels.size(); k++){
            System.out.println(classTagName+srcLabel+"->"+classTagName+dstLabels.get(k) + " [label=\"CF\", color=\"sienna\"]");
        }
    }

    public static ArrayList removeDuplicates(ArrayList<String> dstNamesWD){

        ArrayList<String> dstNames = new ArrayList<String>();

        for (String element : dstNamesWD) { 
            if (!dstNames.contains(element)){ 
                dstNames.add(element); 
            } 
        } 
        return dstNames; 
    }



    // ************************

    // ^^^^^^^^^^^^^^^^^^^^^^^^

    private static void printLastLexicalUse(){
        ArrayList<String> varNames = new ArrayList<String>();
        ArrayList<String> startLabels = new ArrayList<String>();
        ArrayList<String> endLabels = new ArrayList<String>();
        String varName = "";
        String startLabel = "";

        for(int i=0; i<LineNum.size(); i++){

            String locallabel = LineNum.get(i)+i;
            String localrule = Type.get(i);
            String localcontent = Content.get(i);
            String localline = Integer.toString(CodeLine.get(i));
            String localcharpos = Integer.toString(CharPos.get(i));

            if("localVariableDeclarationStatement".equals(localrule)){

                RuleContext varctx = getctxForCombination(mctx, locallabel, localrule, localcontent, localline, localcharpos);
                varNames = getExpNamesByDeclaration(varctx);

                if(varNames.size() > 1){
                    System.out.println("ERR: Multiple variables found in localVariableDeclarationStatement");
                } else {
                    varName = varNames.get(0);
                }

                //System.out.println(varName);

                startLabels = getExpLabelsByDecl(varctx, varName);
                if(startLabels.size() > 1){
                    System.out.println("ERR: Multiple labels found for variable: " + varName + " in localVariableDeclarationStatement");
                } else if (startLabels.size() == 1) {
                    startLabel = startLabels.get(0);
                }

                RuleContext parentctx = varctx.getParent().getParent();
                endLabels = getExpLabels(parentctx, varName);

                if(endLabels.size() > 0){
                    System.out.println(classTagName+startLabel+"->"+classTagName+endLabels.get(0) + " [label=\"LLU\", color=\"orange\"]");
                    for(int j=0; j<(endLabels.size()-1); j++){
                        System.out.println(classTagName+endLabels.get(j)+"->"+classTagName+endLabels.get(j+1) + " [label=\"LLU\", color=\"orange\"]");
                    }
                }
            }
        }
    }

    // ^^^^^^^^^^^^^^^^^^^^^^^^

    // ########################

    private static void printLabel(){
        for(int i=0; i<LineNum.size(); i++){

            String content = Content.get(i);
            content = content.replaceAll("\"", "<''>");

            System.out.println(classTagName+LineNum.get(i)+i+"[label=\""+Type.get(i)+"\\n "+content 
            
            +"\\n (line: " + CodeLine.get(i) + ")"
            +"\\n (charpos: " + CharPos.get(i) + ") \"]");
        }
    }

    private static int getPos(int n, int limit){
        int pos = 0;
        for(int i=0; i<limit;i++){
            if(Integer.parseInt(LineNum.get(i))==n){
                pos = i;
            }
        }
        return pos;
    }
}