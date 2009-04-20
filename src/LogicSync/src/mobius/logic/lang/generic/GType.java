/**
 * 
 */
package mobius.logic.lang.generic;


public class GType {

  private final static String Unknown = "[?]";
  private String name; 
  private GType next;
  private GType last;
  
  
  public String toString() {
    StringBuilder blder = new StringBuilder();
    blder.append(name);
    GType curr = next;
    while (curr != null) {
      blder.append(" -> ");
      blder.append(curr.name);
      curr = curr.next;
    }
    return blder.toString();
  }
  public boolean isUnknown() {
    return getArity() == 1 && name.equals(Unknown);
  }
  
  public GType unify(int idx, GType t) {
    if (t.getArity() == 1) {
      if (idx > getArity()) {
        return null;
      }
      final String target = t.get(0);
      if (get(idx).equals(target)) {
        return this;
      }
      else if (get(idx).equals(Unknown)) {
        set(idx, target);
        return this;
      }
      else if (target.equals(Unknown)) {
        t.set(0, get(idx));
        return this;
      }
    }
    return null;
  }
  private int getArity() {
    GType curr = this;
    int i = 0;
    while (curr != null) {
      i++;
      curr = curr.next;
    }
    return i;
  }
  private void set(int idx, String target) {
    if (idx == 0) {
      name = target;
    }
  }
  private String get(int idx) {
    int i = idx;
    GType curr = this;
    while (curr != null && i != 0) {
      i--;
      curr = curr.next;
    }
    return curr.name;
  }
  
  
  public GType(String ...a) {
    last = this;
    assert (a.length > 1);
    name = a[0];
    for (int i = 1; i < a.length; i++) {
      add(a[i]);
    }
  }

  public GType(GType t) {
    this(t.name);
    addAll(t.next);
  }
  
  
  public void add(String s) {
    add(new GType(s));
  }
  private void add(GType typ) {
    last = typ.last;
    if (next == null) {
      next = new GType(typ);
    }
    else {
      next.add(typ);
    }
  }
  
  /**
   * Do a deep copy while adding.
   * @param typ
   */
  public void addAll(GType typ) {

    if (typ != null) {
      final GType newTyp = new GType(typ);
      last.add(newTyp);
    }
  }
  

  public static GType getUnknown() {
    return new GType(Unknown);
  }
  
  /**
   * Sets a specific arity for an Unknown type.
   * @param arity the desired arity
   */
  public void setArity(final int arity) {
    assert (isUnknown());
    for (int i = 1; i < arity; i++) {
      add(Unknown);
    }
  }
  
  
  public GType getReturn() {
    return last;
  }
}