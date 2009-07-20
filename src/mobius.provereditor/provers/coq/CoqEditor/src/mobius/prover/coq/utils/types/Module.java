package mobius.prover.coq.utils.types;

import mobius.prover.coq.CoqProverTranslator;
import mobius.prover.gui.editor.ProverEditor;


/**
 * A node representing a module or a module type.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Module extends CoqType {
  
  /** the name of the module. */
  private String fShortName;

  /**
   * Construct a node representing a module or a module type.
   * @param editor the current prover editor
   * @param name the name of the module of the form: 
   * <code>Module ModuleName</code> or
   * <code>Module Type ModuleName</code> 
   * @param start the line where the module has been discovered
   */
  public Module(final ProverEditor editor, 
                final String name, 
                final int start) {
    super(editor, name.trim());  

    final String [] tab = toString().split(" ");
    fShortName = tab[1];
    if (tab[1].equals("Type")) {
      fShortName = tab[2];
    }
    setImage(CoqProverTranslator.imgs[0]);
    setOffset(start);
  }

  /**
   * Returns the module name.
   * @return a valid module name
   */
  public String getShortName() {
    return fShortName;
  }
  
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return super.toString();
  }
  

  
}
