
public class HeavyweightAnnotation {
	/*@ public behavior
	  @ {|
	  @  requires x > 0;
	  @  requires x == 1;
	  @  ensures \result * \result == x;
	  @  signals (java.lang.Exception e) e != null;
	  @  signals (java.lang.Throwable t) t != null;
	  @ also
	  @  requires x < 0;
	  @  ensures \result > 0;
	  @  signals_only (java.lang.Exception);
	  @ |}
	  @*/
	public static int sqrt(int x) throws Exception {
		return 0;
	}
}
