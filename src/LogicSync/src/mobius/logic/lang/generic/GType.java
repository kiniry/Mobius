package mobius.logic.lang.generic;

/**
 * Class to represent Generic Types.
 * @author J. Charles (julien.charles@gmail.com)
 */
public class GType {
  /** the symbol representing the unknown type. */
  public static final String Unknown = "[?]";
  public static final String TopType = "[T]";
  /** the current name of this type. */
  private String name;
  /** the next type element. */
  private GType next;
  /** the last element of this type. */
  private GType last;
  
  
  /** {@inheritDoc} */
  public String toString() {
    final StringBuilder blder = new StringBuilder();
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
  
  public boolean isElemUnknown() {
    return name.equals(Unknown);
  }
  
  public boolean isUnknown(int idx) {
    return get(idx).equals(Unknown);
  }
  
  public boolean unify(int idx, GType t) {
    if (t.getArity() == 1) {
      if (idx > getArity()) {
        return false;
      }
      final String target = t.get(0);
      if (get(idx).equals(target)) {
        return true;
      }
      else if (get(idx).equals(Unknown)) {
        set(idx, target);
        return true;
      }
      else if (target.equals(Unknown)) {
        t.set(0, get(idx));
        return true;
      }
    }
    return false;
  }
  
  
  public int getArity() {
    GType curr = this;
    int i = 0;
    while (curr != null) {
      i++;
      curr = curr.next;
    }
    return i;
  }

  public GType getNext() {
    return next;
  }

  public String getName() {
    return name;
  }

  public boolean isLast() {
    return this == last;
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
  
  public boolean isTopType() {
    return isTopTypeName() && (next == null);
  }
  public boolean isTopTypeName() {
    return name.equals(TopType);
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
  public void addAll(final GType typ) {

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
  
  /**
   * True if this type has an unknown type in it hierarchy.
   * @return true if contains [?]
   */
  public boolean hasUnknown() {
    if (isElemUnknown()) {
      return true;
    }
    if (next != null) {
      return next.hasUnknown();
    }
    return false;
  }


  public static GType getTopType() {
    return new GType(TopType);
  }
}
