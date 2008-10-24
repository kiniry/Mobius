package mobius.directVCGen.formula;

import java.util.HashMap;


public abstract class Decoration {
  
  private HashMap<PositionHint, Object> hs = 
    new HashMap<PositionHint, Object>();
  
  private String fName;
  
  public Decoration(final String str) {
    fName = str;
  }

  protected Object get(PositionHint n) {
    return hs.get(n);
  }

  protected void set(PositionHint n, Object res) {
    hs.put(n, res);
  }


}
