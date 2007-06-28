public interface Gendered {
  //@ model instance String gender;

  //@ ensures \result == gender.equals("female");
  /*@ pure @*/ boolean isFemale();
}
