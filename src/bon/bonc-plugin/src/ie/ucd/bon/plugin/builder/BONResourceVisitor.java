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

    //System.out.println("Visiting " + resource);
    if (resource.isHidden() || resource.isDerived()) {
      //System.out.println("Not visiting hidden or derived");
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

}
