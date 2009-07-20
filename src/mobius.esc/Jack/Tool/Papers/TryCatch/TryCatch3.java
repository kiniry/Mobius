class TryCatch {

    int [] key = new int[5];

    public void cheat() {
	sneakyMethod();
        System.out.println ("don't worry");
    }


    public void sneakyMethod() {
	try{ 
	    int r = 36; 
	    decrypt(key, r);                                           
	    }           
	finally{
	    return;
	}
    }


    //@ requires access_code < 10;
    public void decrypt(int [] key, int access_code){
    }
}

class TryCatch3 {


    public static void main(String [] args) {
	TryCatch t = new TryCatch();
	t.cheat();
    }


}
