package fr.inria.everest.coq.editor.utils.types;


import mobius.prover.gui.editor.ProverEditor;
import mobius.prover.gui.editor.outline.types.ProverType;

import org.eclipse.swt.graphics.Image;


public class CoqType extends ProverType {
  /** the name of the node. */
  private String fName;
  /** the image used for the node. */
  private Image fImg;
  
  public CoqType(final ProverEditor editor) {
    this(editor, null);
  }
  
  public CoqType(final ProverEditor editor, 
                 final String name) {
    super(editor);
    fName = name;
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return fName;
  }
  
  protected void setName(final String name) {
    fName = name;
  }
  protected void setImage(final Image img) {
    fImg = img;
  }
  public void setEnd(final int end) {
    setLength(end - getOffset());
  }

  public Image getImage() {
    return fImg;  
  }
}

