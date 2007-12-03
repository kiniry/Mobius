package mobius.prover.gui.editor.outline.types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import mobius.prover.gui.editor.ProverEditor;

import org.eclipse.swt.graphics.Image;


public class ProverType {
  private List<ProverType> fSubtypes = new ArrayList<ProverType>();
  private ProverType fSupertype;
  
  private int fOffset;
  private int fLength;
  private ProverEditor fEditor;

  private String fPath = toString();
  
  public ProverType(final ProverEditor editor) {
    fEditor = editor;
  }
  
  public int getLength() {
    return fLength;
  }

  protected void setLength(final int length) {
    fLength = length;
  }

  public int getOffset() {
    return fOffset;
  }

  protected void setOffset(final int offset) {
    fOffset = offset;
  }

  public void add(final ProverType pt) {
    fSubtypes.add(pt);
    pt.fSupertype = this;
    pt.addPath(getPath());
  }



  public Object [] getSubtypes() {
    return fSubtypes.toArray();
  }
  public Object getSupertype() {
    return fSupertype;
  }
  public Image getImage() {
    return null;
  }

  public void selectAndReveal() {  
    //System.out.println(fOffset + " " + fLength);
    if (fOffset != 0 || fLength != 0) {
      fEditor.selectAndReveal(fOffset, fLength);
    }
  }

  public String getPath() {
    return fPath;
  }
  private void addPath(final String path) {
    fPath = path + "." + toString();
  }  
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return "root";
  }

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
