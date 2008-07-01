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
  
  /** an hashmap containing all the elements created, with their corresponding resource. */
  private static Map<IResource, AWorkspaceElement> instances  = 
    new HashMap<IResource, AWorkspaceElement>();
  
  private List<AWorkspaceElement> children = new ArrayList<AWorkspaceElement>();
  private AWorkspaceElement fParent;
  private IResource fKey;
  
  public AWorkspaceElement(final IResource key) {
    instances.put(key, this);
    fKey = key;
  }
  


  
  
  public static AWorkspaceElement getElement(final IResource key) {
    return instances.get(key);
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
    instances.remove(fKey);
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
  
  /**
   * Creates a child from a given resource.
   * @param res the resource to represent as a child
   * @return the child, or <code>null</code>
   */
  public abstract AWorkspaceElement createChildFromResource(IResource res);

  
  public static Project [] createProjectItem(final IProject [] projects) {
    final Project [] tab = new Project[projects.length];
    for (int i = 0; i < projects.length; i++) { 
      tab[i] = new Project(projects[i]);
    }
    return tab;
  }
}
