package experiments;
public class Test {
  public String old_str = "abc";
  public String str = "aaa";
  public static String sss;
  
  //@ requires 5 == 2;  
  public static void dupa(){
    int k = 3;
  }
  
  //@ requires 2 == 2;  
  public static void main(/*@ non_null */String[] args) throws Exception {
    Test2 test = new Test2();
    test.abc = "s";
    //test.efg = "aa";
    test.abc = "23";
    sss = "";
    //@ assert sss != null;
    
    //@ assert this != null;
    //@ assert 2 + 2*(1+4) < 5;
    //@ assert 2 + 2*(1+4) > 123412;
    // @ ghost int x = 4;
    // @ ghost int y = 5;
    // @ assert x + y < 11;
    // @ assert (x > y ? x < 2 : y > x - 3);
    // @ assert true;
    // @ non_null
    int a = 1, b = 2;
    int c;
    c = a + b;
    //@ assert 2 + 2*(1+4) > 123412;
    int[] d = null;
    //@ assert d.length < 123;
    //@ assert (\forall int k; k >=0 && k < 10 ==> d[k] != a);
    d[0] = 1;
    for (int i = 0; i <1 ; i++);
    for (int j = 0; j < 1; j ++);
    for (int i = 0; i <1 ; i++);
    //Object x = new Object(){public String toString(){int mmm = 12;return null;}};
  }
  
  public int a(){
    //@ assert 1 == 1;
    return 3;
    //@ assert 2 == 2;
  }
  private class Klasa{
    private int abc;
  }
}
