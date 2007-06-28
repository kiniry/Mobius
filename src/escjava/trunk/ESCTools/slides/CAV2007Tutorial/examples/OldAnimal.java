public class OldAnimal extends Animal {
  //@ public invariant 65 < age;

  //@ requires g.equals("female") || g.equals("male");
  //@ assignable gender, age;
  //@ ensures gender.equals(g) && age == 66;
  public OldAnimal(String g) { super(g); age = 66; }
}
