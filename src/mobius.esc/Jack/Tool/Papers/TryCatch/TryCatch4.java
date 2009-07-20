class InnocentException extends Exception {}

class TryCatch {

    int x = 1;

    //@ invariant x > 0;

    int [] key = new int[5];

    public void cheat() {
	try {sneakyMethod3();}
	catch (InnocentException e) {System.out.println ("don't worry");}
    }


    public void sneakyMethod1() {
	int r = 36; 
	decrypt(key, r);                                           
    }
    


    public void sneakyMethod3() throws InnocentException {
	try{ 
	    x = -3;
	    decrypt(key, x);                                           
	    }           
	finally{
            x = 1;
	    throw new InnocentException();
	}
    }

    public void sneakyMethod2() {
	try{ 
	    int r = 36; 
	    decrypt(key, r);                                           
	    }           
	catch (Error e){
	}
    }

    //@ requires access_code < 10;
    public void decrypt(int [] key, int access_code){
    }
}

class TryCatch4 {


    public static void main(String [] args) {
	TryCatch t = new TryCatch();
	t.cheat();
    }


}
