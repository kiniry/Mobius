package mobius.prover.gui.editor.outline.types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.swt.graphics.Image;

/**
 * Base class to handle keywords corresponding to specific editor entries.
 * It also handles a hierarchy structure.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProverType {
  /** the list of subtypes of this type. */
  private final List<ProverType> fSubtypes = new ArrayList<ProverType>();
  /** the super type of this type. */
  private ProverType fSupertype;
  
  /** the offset of the part this node is attached to. */
  private int fOffset;
  /** the length of the part this node is attached to. */
  private int fLength;
  
  /** the editor associated to this node. */
  private final ProverEditor fEditor;

  /** the path to the node. */
  private String fPath = toString();
  
  /**
   * Initialize a node, associating it to an editor.
   * @param editor the editor to which this node is attached.
   * Not <code>null</code>
   */
  public ProverType(final ProverEditor editor) {
    fEditor = editor;
  }

  /**
   * Sets the offset.
   * @param offset a valid offset
   */
  protected void setOffset(final int offset) {
    if (offset >= 0) {
      fOffset = offset;
    }
  }
  
  /**
   * Sets the length.
   * @param length a valid length
   */
  protected void setLength(final int length) {
    if (length >= 0) {
      fLength = length;
    }
  }

  /**
   * Returns the offset.
   * @return a positive number
   */
  public int getOffset() {
    return fOffset;
  }
  
  /**
   * Returns the length.
   * @return a positive number
   */
  public int getLength() {
    return fLength;
  }
  


  /**
   * Adds a type as a subtype of the current node.
   * @param pt the type to add as a subtype
   */
  public void add(final ProverType pt) {
    fSubtypes.add(pt);
    pt.fSupertype = this;
    pt.addPath(getPath());
  }


  /**
   * Returns an array containing the subtypes of  the node.
   * The subtypes are its children.
   * @return not <code>null</code>
   */
  public Object [] getSubtypes() {
    return fSubtypes.toArray();
  }
  /**
   * Returns the supertype of the node.
   * @return An object or <code>null</code>
   */
  public ProverType getSupertype() {
    return fSupertype;
  }
  
  
  /**
   * Returns a valid image representing the node.
   * @return <code>null</code>
   */
  public Image getImage() {
    return null;
  }

  /**
   * Show the part of the editor corresponding to
   * the node.
   */
  public void selectAndReveal() {  
    //System.out.println(fOffset + " " + fLength);
    if (fOffset != 0 || fLength != 0) {
      fEditor.selectAndReveal(fOffset, fLength);
    }
  }

  /**
   * Returns the path of the node.
   * @return a String, or root...
   */
  public String getPath() {
    return fPath;
  }
  
  /**
   * Adds a prefix to the path.
   * @param path the prefix to add
   */
  private void addPath(final String path) {
    fPath = path + "." + toString();
  }  
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return "root";
  }

  /**
   * Returns the type which is a child from this node.
   * @param path the path to retreive the child
   * @return the type if it exists or <code>null</code>
   */
  public ProverType findFromPath(final String path) {
    ProverType res = null;
    if (!path.startsWith(fPath)) {
      res = null;
    }
    else if (path.length() == fPath.length()) {
      res = this;
    }
    else {
      final Iterator<ProverType> iter = fSubtypes.iterator();
      while (iter.hasNext()) {
        final ProverType pt = (ProverType)iter.next();
        final ProverType typ = pt.findFromPath(path);
        if (typ != null) {
          res = typ;
        }
      }
    }
    return res;
  }
  
}
