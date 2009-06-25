package mobius.directvcgen.ui.poview.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;

/**
 * The base class to represent all nodes.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public abstract class AWorkspaceElement  {
  
  /** an hashmap containing all the elements created, with their corresponding resource. */
  private static Map<IResource, AWorkspaceElement> instances  = 
    new HashMap<IResource, AWorkspaceElement>();
  
  /** the children of the node. */
  private List<AWorkspaceElement> fChildren = new ArrayList<AWorkspaceElement>();
  /** the parent of this node or null. */
  private AWorkspaceElement fParent;
  /** 
   * the resource associated with this node. 
   * There is a one to one relationship between nodes and resources. 
   */
  private IResource fKey;
  
  
  /**
   * Construct a node from its associated key.
   * @param key the key associated with this node shall not be null
   */
  public AWorkspaceElement(final IResource key) {
    instances.put(key, this);
    fKey = key;
  }
  

  /**
   * Returns the node associated with the given ressource.
   * @param key the ressource to fetch the corresponding node from
   * @return an element if it exists
   */
  public static AWorkspaceElement getElement(final IResource key) {
    return instances.get(key);
  }
  
  /**
   * Return the name of the node. It is used to print the label
   * associated with the node in the tree view.
   * @return please something meaningful and not too long
   */
  public abstract String getName();
  
  /**
   * Adds a child to this node.
   * @param pe the child to add, it must be valid and fully initialized
   */
  public void add(final AWorkspaceElement pe) {
    fChildren.add(pe);
    pe.fParent = this;
  }
  
  /**
   * Returns the parent of this node.
   * @return the parent or null if this node is a root node.
   */
  public AWorkspaceElement getParent() {
    return fParent;
  }

  /**
   * Returns an array of the children of this node.
   * @return a valid array
   */
  public Object[] getChildren() {
    return fChildren.toArray();
  }
  
  /**
   * Returns an array of children.
   * @return the array of the children of this node
   */
  public AWorkspaceElement [] getElementChildren() {
    return fChildren.toArray(new AWorkspaceElement[0]);
  }
  
  
  /**
   * Returns the number of children of this node.
   * @return a number above or equal to zero
   */
  public int getChildrenCount() {
    return fChildren.size();
  }
  
  /**
   * Returns the image representing the node.
   * @return An image of the enum 
   * {@link mobius.directvcgen.ui.poview.util.ImagesUtils.EImages}
   */
  public Image getImage () {
    return EImages.DEFAULT.getImg();
  }
  
  
  /**
   * Notify an Update to this element and its children.
   */
  public abstract void update();
  
  /**
   * Remove the current node from the list of instances.
   */
  public void remove() {
    instances.remove(fKey);
    for (AWorkspaceElement we : fChildren) {
      we.remove();
    }
  }
  
  
  /**
   * A standard method to update the children by adding/removing
   * the modified nodes.
   * @param res the array containing the resources to update
   */
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
  
  
  /**
   * Removes of the elements from the list from the instance group.
   * @param l the list of elements to remove
   */
  private static void cleanUp(final List<AWorkspaceElement> l) {
    for (AWorkspaceElement we: l) {
      we.remove();
    }
  }
  
  /**
   * Creates a child from a given resource.
   * @param res the resource to represent as a child
   * @return the child, or <code>null</code>
   */
  public abstract AWorkspaceElement createChildFromResource(IResource res);

  
  /**
   * Creates the projects nodes from the given list of projects.
   * It also creates all the necessary children.
   * @param projects the array from which to create the projects nodes
   * @return The projects nodes corresponding to the arguments
   */
  public static Project [] createProjectItem(final IProject [] projects) {
    final Project [] tab = new Project[projects.length];
    for (int i = 0; i < projects.length; i++) { 
      tab[i] = new Project(projects[i]);
    }
    return tab;
  }
  
  
  /**
   * Tells to all the leafs to compile, itself.
   * @param viewer the viewer that asked the nodes to compile
   */
  public void compile(final TreeViewer viewer) {
    final AWorkspaceElement [] tab = getElementChildren();
    for (int i = 0; i < tab.length; i++) {
      tab[i].compile(viewer);
    }
  }


  /**
   * Tells whether the evaluation button should be enabled.
   * @return a boolean
   */
  public boolean isEvaluateEnabled() {
    return true;
  }
}
