package mobius.prover.gui.editor.outline.types;

import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.swt.graphics.Image;


public class FileType extends ProverType {
  private final String fName;
  private final Image fImg;
  
  public FileType(final ProverEditor editor, 
                  final String name, 
                  final Image image) {
    super(editor);
    fName = name;
    fImg = image;
  }
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return fName;
  }
  
  /** {@inheritDoc} */
  @Override
  public Image getImage() {
    return fImg;
  }
}
