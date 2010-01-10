package zoo.enclosure;
  
import java.io.Serializable;
import java.util.List;

import zoo.animal.Animal;  

/**
 * A generic class for a cage that can hold all types of animals.
 * @author Evka
 * @version 1.0
 * @param <T> Type of animal that this cage is for.
 */
public class Cage <T extends Animal & Serializable & Comparable> {
  public int _height;
  public int _width;
  public int numSnakes;
  public int numMice;
  public int numBugs;
  public int numCats;
  public List <T> occupants;
  public int count;
  public final int MAX_CAPACITY = 50;    
  
  //@requires occupants.size() < MAX_CAPACITY;
  //@ensures count == \old(count) + 1;
  //@ensures Math.pow(_height, _width) < 100;
  //@ensures \result == (numSnakes + numBugs - numCats) * numMice;
  public void putIn(T newOccupant) {  }    
  
  /*@ public normal_behavior 
  @ requires count > 0 && occupants.contains(toGo);
  @ assignable occupants; 
  @ ensures 0 <= \result && count != \old(count)
  @ && \result * \result <= count;
  @ also
  @ public normal_behavior
  @   requires toGo == null;
  @   assignable \nothing;
  @   signals_only NullPointerException;
  @*/      
  public void remove(T toGo) { }
  
  //@requires !(_height + _width != 50); 
  //@requires _height + _width == 90;
  //@requires _height % 10 == 0;
  //@requires _width / 25 <= 5;
  //@requires numCats - numMice > 0;
  public void enlarge(int height) {}
  
  
  
  /*@ behavior
  forall String s;
  old String oldString = ss;
  requires occupants[2] != null;
  measured_by \not_specified;
  diverges true;
  when true;
  accessible _width;
  assignable _height;
  captures occupants;
  callable paint;
  ensures _width < _height;
  signals_only CloneNotSupportedException;
  signals (NullPointerException) occupants == null;
  working_space 100;
  duration 1000l;
  @*/ 
  public /*@ pure @*/ void countAll(){}
  
  //@requires +color > 0;  
  //@requires -color < 0 ^ +color > 0; 
  public void paint(int color) {}
  
 // public List < String > getAnimalNames() {return null;}
  
  //@invariant numCats > numMice;
  //@invariant numBugs < 100;
  //@invariant numMice >= 50;
  //@invariant numSnakes <= 10;
  //@constraint numCats > \old(numCats);
  
}  
  