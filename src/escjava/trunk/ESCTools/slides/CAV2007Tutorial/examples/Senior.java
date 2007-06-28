public class Senior extends Person {
  /*@ also
    @   requires 65 < a && a <= 150;
    @   assignable age;
    @   ensures age == a;
    @*/
  public void setAge(final int a) { super.setAge(a); }

  //@ requires g.equals("female") || g.equals("male");
  //@ assignable gender, age;
  //@ ensures gender.equals(g) && age == 66;
  public Senior(final String g) { super(g); age = 66; ageDiscount = true; }
}
