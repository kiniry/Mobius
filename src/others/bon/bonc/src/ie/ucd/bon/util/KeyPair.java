package ie.ucd.bon.util;

public class KeyPair<A, B> {

  public static final int SHIFT_FACTOR_A = 0;
  public static final int SHIFT_FACTOR_B = 4;
  
  public A a;
  public B b;
  
  public KeyPair(A a, B b) {
    this.a = a;
    this.b = b;
  }

  public A getA() {
    return a;
  }

  public B getB() {
    return b;
  }

  @Override
  public int hashCode() {
    return (a.hashCode() << SHIFT_FACTOR_A) + (b.hashCode() << SHIFT_FACTOR_B);
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof KeyPair) {
      KeyPair<?,?> other = (KeyPair<?,?>)obj;
      return this.a.equals(other.a) && this.b.equals(other.b);      
    } else {
      return false;
    }
  }
  
  
  
}
