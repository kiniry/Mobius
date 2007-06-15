
package mobius.directVCGen.vcgen.struct;

import escjava.sortedProver.Lifter.Term;

/**
 * A structure to represent the postcondition associated with a given exception.
 * @author J. Charles and B. Grégoire
 */
public class ExcpPost {
  /** the type of the exception to which correspond the postcondition */
  public final /*@ non_null @*/ Term type;
  /** the post condition that is verified if the specified exception is triggered*/
  public final /*@ non_null @*/ Post post;

  /**
   * Construct an exceptional postcondition from an exception type
   * and a given postcondition
   * @param type the type of the exception
   * @param p the postcondition associated with it
   */
  public ExcpPost (Term type, Post p) {
    this.type = type;
    this.post = p;
  }

  /*
   * (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  public String toString() {
    return "( " + type + ", " + post + ")";
  }

}