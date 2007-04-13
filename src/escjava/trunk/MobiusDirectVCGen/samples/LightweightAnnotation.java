import java.lang.Exception;

public class LightweightAnnotation  {

	public int i;
	
	//@ invariant i >= 0; 
	
	/*@ requires x > 0;
	  @ ensures \result * \result == x;
	  @ signals (java.lang.Exception e) e != null;
	  @ signals (java.lang.Throwable t) t != null;
	  @*/
	
	public static int sqrt(int x) throws Exception {
		return 0;
	}

}
