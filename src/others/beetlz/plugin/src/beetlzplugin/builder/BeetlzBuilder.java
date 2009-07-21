package beetlzplugin.builder;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

import beetlzplugin.runner.BeetlzRunner;

public class BeetlzBuilder extends IncrementalProjectBuilder {

	public static final String BUILDER_ID = "BeetlzPlugin.beetlzBuilder";

	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
	 *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	@SuppressWarnings("unchecked")
  protected IProject[] build(int kind, Map args, IProgressMonitor monitor) 
			throws CoreException {
		
	  BeetlzRunner runner = new BeetlzRunner();
	  runner.runChecker(getProject());
	  
		return null;
	}

}
