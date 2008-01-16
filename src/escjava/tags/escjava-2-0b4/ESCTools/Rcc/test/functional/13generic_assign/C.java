class A/*#{ghost Object g}*/ {}

public class C {
  public static final Object a = new Object();
  public static final Object b = new Object();
  
  A/*#{a}*/ x;
  A/*#{b}*/ y;

  void f() {
    x = y;
  }
}

