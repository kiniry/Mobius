package ie.ucd.bon.tester;

public class Tracker {

  private long totalLength;
  
  public Tracker() {
    totalLength = 0;
  }
  
  public void addInput(String input) {
    totalLength += input.length();
  }

  public long getTotalLength() {
    return totalLength;
  }

}
