// $Id$
package escjava.model_classes;

// immutable!
public final /*@ pure @*/ class Bag
{
  //@ public pure model \bigint size();

  // Queries

  public boolean isEmpty() {
    return false;
  }

  public boolean has(Object o) {
    return false;
  }

  public boolean equals(Object o) {
    return this == o;
  }

  // Selectors

  public Object choose() {
    return null;
  }

  public Bag insert(Object o) {
    return null;
  }

  public Bag remove(Object o) {
    return null;
  }

  // Constructors and factory methods

  public static Bag empty() {
    return null;
  }

  // Helpers methods
}

