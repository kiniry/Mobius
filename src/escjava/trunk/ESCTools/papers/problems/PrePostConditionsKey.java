package problems;

class PrePostConditionsKey
{
  byte b;
  int i;
  Object o;
  String s;
  static Object so;
  
  //@ requires o != null;
  //@ ensures o.equals(s.toString());
  //@ signals (Exception) false;
  void m() {
    o = s.toString();
  }
  
  //@ requires Byte.MIN_VALUE <= i && i <= Byte.MAX_VALUE;
  //@ ensures s != null;
  //@ signals (Exception) false;
  void n() {
    b = (byte)i;
    if (b == i)
      s = new String();
    //@ assert s != null;
  }

  //@ requires o != null;
  //@ requires j < Byte.MIN_VALUE && Byte.MAX_VALUE < j;
  //@ ensures o != null;
  //@ signals (Exception) false;
  void o(int j) {
    if (j == b)
      o = null;
    //@ assert o != null;
  }
  
  //@ requires t != null;
  //@ requires t.length >= 6;
  //@ ensures PrePostConditionsKey.so.equals(t.substring(3,6));
  //@ signals (Exception) false;
  void p(String t) {
    PrePostConditionsKey.so = t.substring(3,6);
  }

  //@ requires StaticPreconditionsKey.o != null;
  //@ requires s == StaticPreconditionsKey.s;
  //@ ensures s == StaticPreconditionsKey.s;
  //@ signals (Exception) false;
  void q() {
    if (StaticPreconditionsKey.s.hashCode() >= Integer.MIN_VALUE) {
      StaticPreconditionsKey.s = "foobar";
    }
    assert s == StaticPreconditionsKey.s;
  }
  
  //@ requires o == null;
  //@ requires b < 0;
  //@ ensures i == 2;
  //@ signals (IllegalArgumentException) (\old(o == null));
  //@ signals (IllegalArgumentException iae) (\old(b < 0) && iae.getMessage().equals("bogus byte"));
  void r(Object o, byte b) {
    if (o == null)
      throw new IllegalArgumentException();
    if (b < 0)
      throw new IllegalArgumentException("bogus byte");
    i = 2;
  }
  
  public static void main(String[] args) {
    PrePostConditionsKey ppc = new PrePostConditionsKey();
    ppc.m();
    ppc.n();
    ppc.o(127);
    ppc.p("foobar");
    ppc.q();
  }
}

class StaticPreconditionsKey {
  static int i;
  static String s;
}