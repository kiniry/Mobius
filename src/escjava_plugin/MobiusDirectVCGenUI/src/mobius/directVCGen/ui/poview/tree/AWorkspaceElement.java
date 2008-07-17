package mobius.directVCGen.ui.poview.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.directVCGen.ui.poview.util.ImagesUtils;
import mobius.directVCGen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;


public abstract class AWorkspaceElement  {
  
  /** an hashmap containing all the elements created, with their corresponding resource. */
  private static Map<IResource, AWorkspaceElement> instances  = 
    new HashMap<IResource, AWorkspaceElement>();
  
  private List<AWorkspaceElement> fChildren = new ArrayList<AWorkspaceElement>();
  private AWorkspaceElement fParent;
  private IResource fKey;
  
  public AWorkspaceElement(final IResource key) {
    instances.put(key, this);
    fKey = key;
  }
  


  
  
  public static AWorkspaceElement getElement(final IResource key) {
    return instances.get(key);
  }
  
  /**
   * Return the name of the node. It is used to print the label
   * associated with the node in the tree view.
   * @return please something meaningful and not too long
   */
  public abstract String getName();
  
  public void add(final AWorkspaceElement pe) {
    fChildren.add(pe);
    pe.fParent = this;
  }
  
  public AWorkspaceElement getParent() {
    return fParent;
  }

  public Object[] getChildren() {
    return fChildren.toArray();
  }
  public AWorkspaceElement [] getElementChildren() {
    return fChildren.toArray(new AWorkspaceElement[0]);
  }
  public int getChildrenCount() {
    return fChildren.size();
  }
  public Image getImage () {
    return EImages.DEFAULT.getImg();
  }
  
  public abstract void update();
  
  public void remove() {
    instances.remove(fKey);
    for (AWorkspaceElement we : fChildren) {
      we.remove();
    }
  }
  
  
  protected void update(final IResource[] res) {
    final List<AWorkspaceElement> oldchildren = fChildren;
    fChildren = new ArrayList<AWorkspaceElement>();
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
  
  public void compile(final TreeViewer viewer) {
    final AWorkspaceElement [] tab = getElementChildren();
    for (int i = 0; i < tab.length; i++) {
      tab[i].compile(viewer);
     
    }
  }





  public boolean isEvaluateEnabled() {
    return true;
  }
}
