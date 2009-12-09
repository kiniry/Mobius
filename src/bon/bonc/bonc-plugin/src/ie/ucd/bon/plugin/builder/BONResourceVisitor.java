package ie.ucd.bon.plugin.builder;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;

public class BONResourceVisitor implements IResourceVisitor {

  private final List<IResource> bonResources;

  public BONResourceVisitor() {
    bonResources = new LinkedList<IResource>();
  }

  public boolean visit(IResource resource) throws CoreException {

    if (resource.isHidden() || resource.isDerived()) {
      return false;
    }

    if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("bon")) {
      //System.out.println("BON Resource!");
      bonResources.add(resource);
    }

    return true;
  }

  public List<IResource> getBONResources() {
    return bonResources;
  }
  
  public static List<IResource> getBONResources(IResource resource) {
    BONResourceVisitor v = new BONResourceVisitor();
    try {
      resource.accept(v); 
    } catch (CoreException ce) {
      //Do nothing?
    }
    return v.getBONResources();
  }

}
