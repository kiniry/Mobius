package freeboogie.experiments.graphgen;

public class Counter {

  private int uniqueCount;
  private int count;

  public Counter() {
    uniqueCount = 0;
    count = 0;
  }

  public int getCount() {
    return count;
  }
  
  public void increaseCount() {
     ++uniqueCount;
     ++count;
  }
  
  public void decreaseCount() {
    count--;
  }
  
  public int getUnique() {
    return uniqueCount;
  }
  
}
