package mobius.bico.bicolano;

public class Translation {
  /** the representation of the type. */
  private String fStr;
  
  public Translation(String str) {
    fStr = str;
  }
  public Translation() {
    fStr = "";
  }
  
  public String toString() {
    return fStr;
  }
  
  protected void setStr(String str) {
    fStr = str;
  }
}
