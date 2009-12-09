package ie.ucd.bon.plugin.builder;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

public class BONResourceDeltaVisitor implements IResourceDeltaVisitor {

  private final List<IResource> changedBonResources;

  public BONResourceDeltaVisitor() {
    changedBonResources = new LinkedList<IResource>();
  }
  
  public boolean visit(IResourceDelta delta) throws CoreException {
    
    IResource resource = delta.getResource();
    
    if (resource.isHidden() || resource.isDerived()) {
      return false;
    }

    if (resource.getFileExtension() != null && resource.getFileExtension().equalsIgnoreCase("bon")) {
      changedBonResources.add(resource);
    }
    
    return true;
  }

  public List<IResource> getChangedBonResources() {
    return changedBonResources;
  }

}
