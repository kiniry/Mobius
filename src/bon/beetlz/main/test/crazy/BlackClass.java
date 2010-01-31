package crazy;

/**
 * Here:
 * - simple JML statements
 * @author evka
 *
 */
/*@ nullable_by_default @*/
public class  BlackClass {
  
  public boolean nice;
  public int counter;
  public final int MAXCOUNT = 23;
  public final String NAME = "name"; 
  public String currentColour;
  public String[] colours;
  public int[] numbers;
  
  //@assignable nice, numbers;
  //@requires zwei.length() > 5;
  //@requires zwei.length() < 15;
  //@requires zwei.length() >= 5;
  //@requires zwei.length() <= 15;
  //@requires eins != zwei;
  //@ensures numbers[0] != 0; 
  //@ensures numbers[1] == 0;
  public /*@ non_null @*/ String one(String eins,/*@ non_null @*/ String zwei){return null;}
  
  //@assignable colours;
  //@assignable counter;
  //@assignable currentColour;
  //@requires eins + zwei < 100;
  //@requires eins-zwei > 0;
  //@requires eins * 5 == zwei / 3;
  //@requires eins == 1 ^ 0;
  //@ensures \result % 2 == 0;
  //@ensures - (\result) <= 0;
  //@ensures Math.pow(eins, zwei) == \result;
  //@ensures \result == \old(eins) + \old(zwei);
  public int two(int eins, int zwei, int drei){return 0;}
  
  //@requires !eins;
  //@requires eins && zwei ==> drei;  
  //@requires eins && zwei == true;
  //@requires zwei && drei == false;
  //@ensures (eins && zwei) || drei <==> (drei && nice);
  //@ensures nice && zwei <=!=> counter < 0;
  //@ensures (\result).find("hallo"); 
  public /*@ pure @*/ YellowClass three(boolean eins, boolean zwei, boolean drei){return null;}

  //(not recognized) (int) uno % (int) duo = 0;
  //@requires +uno > 0;
  public /*@ pure @*/ String four(double uno, double duo, double tre) {return null;}
  
  //@invariant counter <= MAXCOUNT;
  //@invariant counter < 50 ==> nice; 
}
