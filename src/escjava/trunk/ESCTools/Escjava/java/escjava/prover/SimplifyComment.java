/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.prover;

/** An object of this class represent a progress comment produced by Simplify.
 ** <p>
 ** 
 ** @see Simplify
 ** @see escjava.prover.CECEnum
 ** @see SExp
 **/

public class SimplifyComment extends SimplifyOutput {
  final String msg;

  public String getMsg() {
    return msg;
  }

  SimplifyComment(String msg) {
    super(COMMENT);
    this.msg = msg;
  }
}
