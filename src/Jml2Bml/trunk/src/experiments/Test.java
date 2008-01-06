package experiments;


public class Test {

  public static void main(/*@ non_null */String[] args) throws Exception {
    //@ ghost int x = 4;
    //@ ghost int y = 5;
    //@ assert x + y < 11;
    //@ assert (x > y ? x < 2 : y > x - 3);
    //@ assert true;
    //@ non_null
    int a = 1, b = 2;
    int c;
    c = a + b;
    int[] d;
    //@assert (\forall int k; 0 <= k && k < 10 ==> d[k] != 2);
  }
}
