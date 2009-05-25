package zoo.enclosure;

import java.io.Serializable;

import zoo.animal.Animal;  

//Use this class for all operators, or as many as we can fit in...
public class Cage <T extends Animal & Serializable & Comparable> {
  public int numSnakes;
  public int numMice;
  public int numBugs;
  public int numCats;
  public Animal[] occupants;
  public int count;
  public int MAX_CAPACITY = 50;
  
  //@requires occupants.lenght < MAX_CAPACITY;
  //@ensures count == \old(count) + 1;
  public void putIn(Animal newOccupant) { }
  
  //@requires count > 0;
  //@requires occupants.contains(toGo);
  //@ensures count != \old(count);
  public void remove(Animal toGo) {}
  
  
  //@invariant numCats > numMice;
  //@invariant numBugs < 100;
  //@invariant numMice >= 50;
  //@invariant numSnakes <= 10;
 
  
}  
  
/*
FOR_ALL(1, "for_all", "\forall"), EXISTS(1, "exists", "\\exists"),
UNARY_PLUS(5, "+", "+"), UNARY_MINUS(5, "-", "-"), NOT(5, "not", "!"),
POWER(10, "^", "Math.pow"),
MULTIPLE(15, "*", "*"), DIVIDE(15, "/", "/"), INT_DIVDE(15, "//", "/"), MODULO(15, "\\", "%"),
PLUS(20, "+", "+"), MINUS(20, "-", "-"),
GREATER(25, ">", ">"), SMALLER(25, "<", "<"), GREATER_EQUAL(25, ">=", ">="), SMALLER_EQUAL(25, "<=", "<="),
EQUAL(30, "=", "=="), NOT_EQUAL(30, "/=", "!="),
AND(35, "and", "&&"), OR(35, "or", "||"),
IMPLIES(40, "->", "->"), //IMPLIES_LEFT(40, "", ""),
IFF(45, "<->", "<==>"), NOT_IFF(45, "not <->", "<=!=>"),
NO_OP(100, "", "");
*/