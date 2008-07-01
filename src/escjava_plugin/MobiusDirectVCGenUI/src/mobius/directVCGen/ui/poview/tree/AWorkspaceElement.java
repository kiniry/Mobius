package mobius.directVCGen.ui.poview.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.directVCGen.ui.poview.IImagesConstants;
import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public abstract class AWorkspaceElement implements IImagesConstants {
  private static Map<IResource, AWorkspaceElement> hm  = 
    new HashMap<IResource, AWorkspaceElement>();
  
  protected List<AWorkspaceElement> children = new ArrayList<AWorkspaceElement>();
  private AWorkspaceElement fParent = null;
  private IResource fKey;
  
  public AWorkspaceElement(final IResource key) {
    hm.put(key, this);
    this.fKey = key;
  }
  


  
  
  public static AWorkspaceElement getElement(final IResource key) {
    return hm.get(key);
  }
  

  public abstract String getName();
  
  public void add(final AWorkspaceElement pe) {
    children.add(pe);
    pe.fParent = this;
  }
  
  public AWorkspaceElement getParent() {
    return fParent;
  }

  public Object[] getChildren() {
    return children.toArray();
  }
  public AWorkspaceElement [] getElementChildren() {
    return children.toArray(new AWorkspaceElement[0]);
  }
  public int getChildrenCount() {
    return children.size();
  }
  public Image getImage () {
    return Utils.getImage(IMG_DEFAULT);
  }
  
  public abstract void update();
  
  public void remove() {
    hm.remove(fKey);
    for (AWorkspaceElement we : children) {
      we.remove();
    }
  }
  protected void update(final IResource[] res) {
    final List<AWorkspaceElement> oldchildren = children;
    children = new ArrayList<AWorkspaceElement>();
    for (int i = 0; i < res.length; i++) {
      AWorkspaceElement pe = getElement(res[i]);
      if (pe == null) {
        pe = createChildFromResource(res[i]);
      }
      if (pe != null) {
        oldchildren.remove(pe);
        add(pe);
      }
    }
      
    cleanUp(oldchildren);
  }
  private static void cleanUp(final List<AWorkspaceElement> children) {
    for (AWorkspaceElement we: children) {
      we.remove();
    }
  }
  
  public abstract AWorkspaceElement createChildFromResource(IResource res);

  public static Project [] createProjectItem(final IProject [] projects) {
    final Project [] tab = new Project[projects.length];
    for (int i = 0; i < projects.length; i++) { 
      tab[i] = new Project(projects[i]);
    }
    return tab;
  }
}
