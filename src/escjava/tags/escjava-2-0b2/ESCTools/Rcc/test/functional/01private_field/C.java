class A {
  public int x;
}

class B {
  private A a;
  public B(A a) { this.a = a; }
}

public class C {
  private B b;
  private A a;

  public void doit() {
    b = new B(a);
    b.a.x = 0;
  }
}
