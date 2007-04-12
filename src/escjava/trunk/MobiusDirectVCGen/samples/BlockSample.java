
public class BlockSample {

  public static void f() {
    int i = 0;
    labl: {
    	i++;
    }
    
     {
    	 i++;
    }
    Throwable o;
    RuntimeException r = new NullPointerException();
    throw r;
    //@ assert i == 1;
  }
}
