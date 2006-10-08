package prover.gui.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import prover.gui.builder.tagger.Tagger;

/**
 * The project build for tags.
 * @author J. Charles
 */
public class ProjectBuilder extends IncrementalProjectBuilder {
	/** the builder id ie.: "prover.editor.builder" */
	public static final String BUILDER_ID = "prover.editor.builder";
	
	/*
	 * (non-Javadoc)
	 * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
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
				IResourceDelta delta = getDelta(getProject());
				delta.accept(new DeltaVisitor());
				break;
			default:
				break;	
		}
		return null;
	}

}
