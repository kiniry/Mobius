package mobius.directVCGen.ui.poview.tree;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;

import mobius.directVCGen.ui.poview.IImagesConstants;
import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.swt.graphics.Image;


public abstract class WorkspaceElement implements IImagesConstants {
	protected List children = new ArrayList();
	private WorkspaceElement parent = null;
	private IResource key;
	private static HashMap hm  = new HashMap();
	public static WorkspaceElement getElement(IResource key) {
		return (WorkspaceElement) hm.get(key);
	}
	
	public WorkspaceElement(IResource key) {
		hm.put(key, this);
		this.key = key;
	}
	public abstract String getName();
	
	public void add(WorkspaceElement pe) {
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
		return (WorkspaceElement []) children.toArray(new WorkspaceElement[0]);
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
		Iterator iter = children.iterator();
		while(iter.hasNext()) {
			((WorkspaceElement) iter.next()).remove();
		}
	}
	protected void update(IResource[] res) {
		List oldchildren = children;
		children = new ArrayList();
		for(int i = 0; i < res.length; i++) {
			WorkspaceElement pe = getElement(res[i]);
			if(pe == null) {
				pe = createChildFromResource(res[i]);
			}
			if(pe != null) {
				oldchildren.remove(pe);
				add(pe);
			}
		}
			
		cleanUp(oldchildren);
	}
	private static void cleanUp(List children) {
		Iterator iter = children.iterator();
		while(iter.hasNext()) {
			WorkspaceElement pe = ((WorkspaceElement)iter.next());
			pe.remove();
		}
	}
	
	public abstract WorkspaceElement createChildFromResource(IResource res);

	public static Project [] createProjectItem(IProject [] projects) {
		Project [] tab = new Project[projects.length];
		for(int i = 0; i < projects.length; i++) { 
			tab[i] = new Project(projects[i]);
		}
		return tab;
	}
}
