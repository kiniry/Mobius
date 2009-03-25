package freeboogie.experiments.graphgen;

public class Counter {

  private int count;

  public Counter() {
    count = 0;
  }

  public int getCount() {
    return count;
  }
  
  public int getIncreasedCount() {
    return ++count;
  }
  
}
