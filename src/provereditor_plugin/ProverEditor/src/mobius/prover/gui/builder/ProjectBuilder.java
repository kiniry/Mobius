package mobius.prover.gui.builder;

import java.util.Map;

import mobius.prover.gui.builder.tagger.Tagger;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;


/**
 * The project build for tags.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class ProjectBuilder extends IncrementalProjectBuilder {
  /** the builder id ie.: "prover.editor.builder". */
  public static final String BUILDER_ID = "prover.editor.builder";
  
  /** {@inheritDoc} */
  @Override
  @SuppressWarnings("unchecked")
  protected IProject[] build(final int kind, 
                             final Map args, 
                             final IProgressMonitor monitor)
    throws CoreException {
    switch(kind) {
      case CLEAN_BUILD :
        Tagger.performCleanBuild(getProject());
        break;
      case FULL_BUILD:
        Tagger.instance.performFullBuild(getProject());
        break;
      case INCREMENTAL_BUILD:
      case AUTO_BUILD:
        final IResourceDelta delta = getDelta(getProject());
        delta.accept(new DeltaVisitor());
        break;
      default:
        break;  
    }
    return null;
  }

}
