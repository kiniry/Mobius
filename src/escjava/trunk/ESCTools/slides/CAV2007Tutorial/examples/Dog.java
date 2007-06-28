public abstract class Dog extends Animal {
  public static final int D2PY = 7;   // conversion factor
  private /*@ spec_public @*/ int dogAge = 0; //@ in age;
  //@ public invariant dogAge == D2PY*age;

  //@ assignable \nothing;
  //@ ensures \result == dogAge;
  public int getDogAge() { return dogAge; }

  public void setAge(final int a) { super.setAge(a); dogAge = D2PY*age; }
  /* ... */

  //@ requires g.equals("female") || g.equals("male");
  //@ assignable gender;
  //@ ensures gender.equals(g);
  public Dog(final String g) { super(g); }
}
