package mobius.prover.coq.utils.types;

import mobius.prover.gui.editor.ProverEditor;

/**
 * A node representing a require statement.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Require extends CoqType {
  /**
   * Construct a require.
   * @param editor the current instance of provereditor
   * @param name the name of the node,
   * which is of the form <code>Require Import module</code>
   */
  public Require(final ProverEditor editor, final String name) {
    super(editor, name);
  }
  

}
