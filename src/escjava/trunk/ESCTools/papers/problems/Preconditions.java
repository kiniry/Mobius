class Preconditions
{
  byte b;
  int i;
  Object o;
  String s;
  
  //@ requires ?
  void m() {
    o = s.toString();
  }

  void n() {
    b = (byte)i;
    if (b == i)
      s = new String();
    //@ assert s != null;
  }

  void o(int j) {
    if (j == b)
      o = null;
    //@ assert o != null;
  }

  void p(String t) {
    s = t.substring();
  }
}
