package defaultpackage;


import zoo.animal.Animal;

/**
 * @author evka
 *
 */

public /*@ nullable_by_default pure @*/ class ZooClass extends Thread {  

  public String zooName;
  public Animal animalOfTheMonth;
  
  //@assignable \everything;
  public void countVisitor(int newNumber) {}
  
  //public /*@ non_null @*/ String giveInformation() {return null;}
  public String giveInformation() {return null;}
}
