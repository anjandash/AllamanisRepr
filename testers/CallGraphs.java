package testers;

public class CallGraphs
{
	public static void main(String[] args) {
		doStuff();
		testmain();
	}
	
	public static void doStuff() {
		new A().foo();

		int x = 5; 
		int y = 5;
		int z = new GetValue().getInt();

		int a = foo(x, y);
		int b = 20;
		if(a>0 && b>0) {
			while(a>0){
				System.out.println(a);
				a--;	
			}
		} else {
			System.out.println(b);
		}
	}
	
	public static void testmain() {
		
		int x = 10;
		int y = -4;
		
		while(x > 0) {
			x = x+x+y;
		}
			
	}
	
    private static int foo(int a, int b) {
        return (a+b);
    }
    
}

class A
{
	public void foo() {
		bar();
	}
	
	public void bar() {
	}
}