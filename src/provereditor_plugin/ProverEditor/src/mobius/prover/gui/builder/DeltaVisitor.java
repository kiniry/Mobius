package mobius.prover.gui.builder;

import mobius.prover.gui.builder.tagger.Tagger;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;


/**
 * The delta visitor used by the tags builder.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class DeltaVisitor implements IResourceDeltaVisitor {

  /** {@inheritDoc} */
  @Override
  public boolean visit(final IResourceDelta delta) throws CoreException {
    final IResource res = delta.getResource();
    final int type = res.getType();
    final Tagger tag = Tagger.instance;
    if (type == IResource.FILE) {
      switch(delta.getKind()) {
        case IResourceDelta.ADDED:
        case IResourceDelta.CHANGED:
          tag.performAddChangedFile((IFile) res);
          break;
        case IResourceDelta.REMOVED:
          tag.performRemoveFile((IFile) res);
          break;
        default:
          break;
      }
    }
    return true;
  }

}
