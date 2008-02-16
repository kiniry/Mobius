package experiments;

public class Test2 {
  public Test2 parent = new Test2();
  public String abc = null;
  public String efg = null;
  private String ala = null;
  //@ requires ala == null;
  //@ ensures \result < \old(ala);
  public int abc(int i, int j){
    return 17;
  }

}
