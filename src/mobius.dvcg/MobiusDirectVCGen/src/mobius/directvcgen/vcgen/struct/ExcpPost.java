package mobius.directvcgen.vcgen.struct;

import escjava.sortedProver.Lifter.Term;

/**
 * A structure to represent the postcondition associated with a given exception.
 * @author J. Charles (julien.charles@inria.fr),
 *  B. Grégoire (benjamin.gregoire@inria.fr)
 */
public class ExcpPost {
  /** the type of the exception to which correspond the postcondition .*/
  private final /*@ non_null @*/ Term fType;
  /** the post condition that is verified if the specified exception is triggered. */
  private final /*@ non_null @*/ Post fPost;

  /**
   * Construct an exceptional postcondition from an exception type
   * and a given postcondition.
   * @param typ the type of the exception
   * @param pos the postcondition associated with it
   */
  public ExcpPost (final Term typ, final Post pos) {
    fType = typ;
    fPost = pos;
  }


  /**
   * @return a string of the form <code>(type, post)</code>
   */
  @Override
  public String toString() {
    return "( " + getType() + ", " + getPost() + ")";
  }


  /**
   * @return the type
   */
  public /*@ non_null @*/ Term getType() {
    return fType;
  }


  /**
   * @return the post
   */
  public /*@ non_null @*/ Post getPost() {
    return fPost;
  }

}
