package mobius.logic.lang.generic;

import java.util.Iterator;

/**
 * Class to represent Generic Types.
 * @author J. Charles (julien.charles@gmail.com)
 */
public class GType implements Iterable<GType> {
  /** the symbol representing the unknown type. */
  public static final String Unknown = "[?]";
  /** the symbol representing the top type. */
  public static final String TopType = "[T]";
  /** the current name of this type. */
  private String name;
  /** the next type element. */
  private GType next;
  /** the last element of this type. */
  private GType last;
  
  public GType(String a) {
    last = this;
    name = a;
  }

  public GType(GType t) {
    this(t.name);
    addAll(t.next);
  }
  
  /** {@inheritDoc} */
  public String toString() {
    final StringBuilder blder = new StringBuilder();
    if (next != null) {
      for (GType curr: next) {
        blder.append(" -> ");
        blder.append(curr.name);
      }
    }
    return name + blder.toString();
  }
  
  
  public boolean isUnknown() {
    return getArity() == 1 && name.equals(Unknown);
  }
  
  public boolean isElemUnknown() {
    return name.equals(Unknown);
  }
  

  public boolean unify(int idx, GType t) {
    if (t.getArity() == 1) {
      if (idx > getArity()) {
        return false;
      }
      return get(idx).unifyElem(t);
    }
    return false;
  }
  
  
  public boolean unifyElem(GType t) {
    if (t.getArity() == 1) {
      final String target = t.getName();
      if (name.equals(target)) {
        return true;
      }
      else if (name.equals(Unknown)) {
        set(target);
        return true;
      }
      else if (target.equals(Unknown)) {
        t.set(name);
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
  
  private void set(String target) {
    name = target;
  }
    


  private GType get(int idx) {
    int i = idx;
    GType curr = this;
    while (curr != null && i != 0) {
      i--;
      curr = curr.next;
    }
    return curr;
  }
  
  public boolean isTopType() {
    return isElemTopType() && (next == null);
  }
  public boolean isElemTopType() {
    return name.equals(TopType);
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
    for (GType t: this) {
      if (t.isElemUnknown()) {
        return true;
      }
    }
    return false;
  }


  public static GType getTopType() {
    return new GType(TopType);
  }

  public Iterator<GType> iterator() {
    
    return new Iterator<GType>() {
      private GType n = GType.this;

      public boolean hasNext() {
        return n != null;
      }


      public GType next() {
        final GType res = n;
        n = n.next;
        return res;
      }


      public void remove() {
        n = n.getNext();
      }
      
    };
  }
}
