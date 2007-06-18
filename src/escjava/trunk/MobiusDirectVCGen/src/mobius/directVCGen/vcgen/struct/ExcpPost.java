package mobius.directVCGen.vcgen.struct;

import escjava.sortedProver.Lifter.Term;

/**
 * A structure to represent the postcondition associated with a given exception.
 * @author J. Charles (julien.charles@inria.fr),
 *  B. Grégoire (benjamin.gregoire@inria.fr)
 */
public class ExcpPost {
  /** the type of the exception to which correspond the postcondition .*/
  public final /*@ non_null @*/ Term type;
  /** the post condition that is verified if the specified exception is triggered. */
  public final /*@ non_null @*/ Post post;

  /**
   * Construct an exceptional postcondition from an exception type
   * and a given postcondition.
   * @param typ the type of the exception
   * @param pos the postcondition associated with it
   */
  public ExcpPost (final Term typ, final Post pos) {
    type = typ;
    post = pos;
  }


  /**
   * @return a string of the form <code>(type, post)</code>
   */
  @Override
  public String toString() {
    return "( " + type + ", " + post + ")";
  }

}
