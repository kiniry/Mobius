package mobius.directVCGen.formula;

import java.util.HashMap;


public abstract class Decoration {
  private HashMap<PositionHint, Object> hs = new HashMap<PositionHint, Object>();
  public Decoration(String string) {
    // TODO Auto-generated constructor stub
  }

  protected Object get(PositionHint n) {
    return hs.get(n);
  }

  protected void set(PositionHint n, Object res) {
    hs.put(n, res);
  }


}
