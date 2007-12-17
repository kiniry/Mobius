class A {

    A prev;
    int i;

    A(A prev, int i) {
	this.prev = prev;
	this.i = i;
    }

}

class InnocentException extends Exception {
}

class FinallyTest {

    public static void main3 (String [] args) {
        A a;
	try {
	    try { 
		a = new A(null, 0);
	    }
	    finally {
		throw new InnocentException();
	    }
	}
	catch (Exception e) {
	};
    }


    // throws java.lang.StackOverflowError
    public static void main (String [] args) {
	A a = null; int i = 0;
	while (true) {
	    a = new A(a, i); i++;
	}
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
	
