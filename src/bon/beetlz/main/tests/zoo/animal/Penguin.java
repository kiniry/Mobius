package zoo.animal;

import zoo.enclosure.Enclosure;
import zoo.personnels.Food;

public class Penguin {
  
  public final int luckyNumber = 7;
  
  public final Food food = Food.FISH;  
  
  public final int noLuckyNumber;
  
   public Penguin(String name) {  noLuckyNumber = 13; }
   
   public Penguin(String name, int age) {  noLuckyNumber = 13; }
   
   protected Penguin(String name, Enclosure encl){noLuckyNumber = 13; }
   
   private Penguin(int name){noLuckyNumber = 13; }  
   
     
  /*public java.util.Enumeration enumerate() { //should not be picked up
     return new java.util.Enumeration() { 
       public boolean hasMoreElements() {  return true; }
       public Object nextElement() { return null; }
     };  
   }*/
}
