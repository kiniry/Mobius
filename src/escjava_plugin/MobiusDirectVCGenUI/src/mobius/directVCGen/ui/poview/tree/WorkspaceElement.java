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


public abstract class WorkspaceElement implements IImagesConstants {
  protected List<WorkspaceElement> children = new ArrayList<WorkspaceElement>();
  private WorkspaceElement parent = null;
  private IResource key;
  
  public WorkspaceElement(final IResource key) {
    hm.put(key, this);
    this.key = key;
  }
  
  private static Map<IResource, WorkspaceElement> hm  = 
    new HashMap<IResource, WorkspaceElement>();

  
  
  public static WorkspaceElement getElement(final IResource key) {
    return (WorkspaceElement) hm.get(key);
  }
  

  public abstract String getName();
  
  public void add(final WorkspaceElement pe) {
    children.add(pe);
    pe.parent = this;
  }
  
  public WorkspaceElement getParent() {
    return parent;
  }

  public Object[] getChildren() {
    return children.toArray();
  }
  public WorkspaceElement [] getElementChildren() {
    return children.toArray(new WorkspaceElement[0]);
  }
  public int getChildrenCount() {
    return children.size();
  }
  public Image getImage () {
    return Utils.getImage(IMG_DEFAULT);
  }
  
  public abstract void update();
  
  public void remove() {
    hm.remove(key);
    for (WorkspaceElement we : children) {
      we.remove();
    }
  }
  protected void update(final IResource[] res) {
    final List<WorkspaceElement> oldchildren = children;
    children = new ArrayList<WorkspaceElement>();
    for (int i = 0; i < res.length; i++) {
      WorkspaceElement pe = getElement(res[i]);
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
  private static void cleanUp(final List<WorkspaceElement> children) {
    for (WorkspaceElement we: children) {
      we.remove();
    }
  }
  
  public abstract WorkspaceElement createChildFromResource(IResource res);

  public static Project [] createProjectItem(final IProject [] projects) {
    final Project [] tab = new Project[projects.length];
    for (int i = 0; i < projects.length; i++) { 
      tab[i] = new Project(projects[i]);
    }
    return tab;
  }
}
