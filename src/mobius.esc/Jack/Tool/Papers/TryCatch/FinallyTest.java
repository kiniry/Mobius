class A {

    A a = new A();
}

class InnocentException extends Exception {
}

class FinallyTest {

    public static void main (String [] args) {
        A a;
	try {
	    try { 
		a = new A();
	    }
	    finally {
		throw new InnocentException();
	    }
	}
	catch (Exception e) {
	};
	System.out.println ("we leven nog");
    }


    // throws java.lang.StackOverflowError
    public static void main3 (String [] args) {
	A a = new A();
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
	
