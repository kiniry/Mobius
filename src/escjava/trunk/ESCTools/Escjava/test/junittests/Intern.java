public class Intern {
Intern();

public void m() {
  String s = "one";
  String ss = "two";
  String sss = "one";
  //@ assert s.isInterned;
  //@ assert ss.isInterned;
  //@ assert !s.equals(ss);
  //@ assert s.equals(sss);
}

}
