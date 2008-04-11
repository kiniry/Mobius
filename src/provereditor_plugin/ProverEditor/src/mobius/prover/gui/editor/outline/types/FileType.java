package mobius.prover.gui.editor.outline.types;

import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.swt.graphics.Image;

/**
 * Represents a basic node for the outline.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class FileType extends ProverType {
  /** the name of the node. */
  private final String fName;
  /** the image of the node. */
  private final Image fImg;
  
  /**
   * Initialize a node, which hase a given editor as its parent.
   * @param editor the parent editore
   * @param name the name of the node
   * @param image the image of the node
   */
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
