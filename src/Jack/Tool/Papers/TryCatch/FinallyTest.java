class A {
    A a = new A();
}

class FinallyTest {

    public static void main (String [] args) {
	try {
	    try { 
		int i = 0;
		while (true) {
		    Object A = new A();
		    System.out.println (i++);
		}
	    }
	    finally {
		throw new NullPointerException();
	    }
	}
	catch (Exception e) {
	};
	System.out.println ("we leven nog");
    }


    // throws java.lang.StackOverflowError
    public static void main3 (String [] args) {
    }
	

    // print: we leven nog
    public static void main2 (String [] args) {
	try {
	    try { 
		throw new StackOverflowError(); 
	    }
	    finally {
		throw new NullPointerException();
	    }
	}
	catch (Exception e) {
	};
	System.out.println ("we leven nog");
    }

}
	
