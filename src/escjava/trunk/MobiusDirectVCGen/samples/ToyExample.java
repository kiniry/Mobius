
public class ToyExample {
	int f;
	public static class A {
		static int fs = 2;
		public static ToyExample t(int i) {
			return null;
		}
	}
	
  public void f() {
    int i = 1;
    int j;
    ;
    A.t(i).f = ((f = 1) + (A.fs = 0));
    
//    if(i == 0);
    j = i = 2 / i;
//    while (true) {
//    	if(i == 0)
//    		continue;
//    	if(i == 2)
//    		break;
//    	i++;
//    }

    //@ assert i == 1;
  }
}
