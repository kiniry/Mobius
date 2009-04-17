/**
 * 
 */
package mobius.logic.lang.generic;

import java.util.ArrayList;
import java.util.List;

public class GType {

  private final static String Unknown = "[?]";
  private List<String> type = new ArrayList<String>(); 
  public String toString() {
    StringBuilder blder = new StringBuilder();
    for (String t: type) {
      blder.append(" -> ");
      blder.append(t);
    }
    return blder.substring(" -> ".length());
  }
  public boolean isUnknown() {
    return type.size() == 1 && type.get(0).equals(Unknown);
  }
  
  public GType unify(int idx, GType t) {
    if (t.type.size() == 1) {
      if (type.size() == 1) {
        
        return null;
      }
      
      if (type.get(0).equals(t.type.get(0))) {
        GType clone = new GType(this);
        clone.type.remove(0);
        return clone;
      }
    }
    return null;
  }
  public GType(String ...a) {
    for (String t: a) {
      type.add(t);
    }
  }

  public GType(GType t) {
    this(t.type.toArray(new String[t.type.size()]));
  }
  public void add(String s) {
    type.add(s);
  }
  public void add(GType typ) {
    for (String s: typ.type) {
      type.add(s);
    }
  }
  public static GType getUnknown() {
    return new GType(Unknown);
  }
  
  
  public void setArity(int arity) {
    assert (isUnknown());
    for (int i = 1; i < arity; i++) {
      type.add(Unknown);
    }
  }
}