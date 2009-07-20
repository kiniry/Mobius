package mobius.prover.exec.toplevel.exceptions;

import mobius.prover.Prover;

/**
 * If the top level process was killed unexpectedly by the 
 * kernel for instance, this exception shall be thrown.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class TopLevelDeathException extends ToplevelException {
  /** A serial UID to have much more fun... */
  private static final long serialVersionUID = 1L;
  
  /**
   * Create a new exception with the killed top level informations.
   * @param pkind The prover whose top level was killed
   */
  public TopLevelDeathException(final Prover pkind) {
    super(pkind, "Oh no ! TopLevel was killed !");
  }


}
