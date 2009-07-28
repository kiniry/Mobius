// $Id$
package escjava.model_classes;

/**
 * Cons objects are functional list constructors (like in ML).
 * Each Cons has a head and a tail. They are both non-null if the
 * represented list is non-empty and are both null if the represented
 * list is empty.
 *
 * The name Cons is a bit improper. In functional languages a List
 * is either Empty or a Cons, which is made of a head (element) and
 * a Tail (List). Unfortunately the name List is already taken by
 * Java. Furthermore we use this class to also represent Empty
 * using nulls, as described above.
 *
 * @author Patrice Chalin
 * @author Joseph Kiniry
 * @author Radu Grigore
 */

// immutable!
public final /*@ pure @*/ class Cons
{
  private final Object head;
  private final Cons tail;

  //@ invariant (head == null) <==> (tail == null);

  // TODO: Make these work in ESC/Java?
  // invariant (\forall Cons a, b;; a.equals(b) <==> b.equals(a));
  // invariant (\forall Cons a;; a.equals(a));
  // invariant (\forall Cons a, b, c;; a.equals(b) && b.equals(c) ==> a.equals(c));

  /*@ normal_behavior
    @   ensures empty();
    @*/
  public Cons() {
    head = null;
    tail = null;
  }
  
  /*@ normal_behavior
    @  requires head != null;
    @  requires tail != null;
    @  ensures this.head == head;
    @  ensures this.tail == tail;
    @  ensures !empty();
    @*/
  public Cons(final Object head, final Cons tail) {
    this.head = head;
    this.tail = tail;
  }

  /*@ normal_behavior
    @   ensures \result == head;
    @*/
  public /*@ pure */ Object head() {
    return head;
  }

  /*@ normal_behavior
    @   ensures \result == tail;
    @*/
  public /*@ pure */ Object tail() {
    return tail;
  }
  
  /*@ also normal_behavior
    @   requires empty();
    @   ensures \result <==> (other instanceof Cons) &&
    @                        ((Cons)other).empty();
    @ also normal_behavior
    @   requires !empty();
    @   ensures \result <==> (other instanceof Cons) &&
    @                        head().equals(((Cons)other).head()) &&
    @                        tail().equals(((Cons)other).tail());
    @*/
  public boolean equals(Object other) {
    if (!(other instanceof Cons)) {
      return false;
    }
    Cons cons_other = (Cons)other;
    if (empty()) {
      return cons_other.empty();
    }
    return 
      head.equals(cons_other.head()) && 
      tail.equals(cons_other.tail());
  }

  /*@ normal_behavior
    @   ensures \result == (head == null);
    @*/
  public boolean empty() {
    return head == null;
  }
}
