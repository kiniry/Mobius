package beetlzplugin.popup.actions;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

/**
 * Visit resources to find which files we have, borrowed from
 * BONc Plugin.
 */
public class ResourceVisitor implements IResourceVisitor {

  private final List<IResource> my_resources;

  public ResourceVisitor() {
    my_resources = new LinkedList<IResource>();
  }

  public boolean visit(IResource resource) throws CoreException {

    if (resource.isHidden() || resource.isDerived()) {
      return false;
    }

    String ext = resource.getFileExtension();
    if (ext != null && (ext.equalsIgnoreCase("bon") || //$NON-NLS-1$
        ext.equalsIgnoreCase("java"))) { //$NON-NLS-1$
      my_resources.add(resource);
    }

    return true;
  }

  public List<IResource> getResources() {
    return my_resources;
  }

}
