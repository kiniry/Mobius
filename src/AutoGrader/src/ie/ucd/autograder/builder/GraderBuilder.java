package ie.ucd.autograder.builder;

import ie.ucd.autograder.builder.markercollectors.FindBugsMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;

public class GraderBuilder extends IncrementalProjectBuilder {

  public static final String BUILDER_ID = "AutoGrader.builder";

  private final FindBugsMarkerCollector findBugsCollector;
  private final List<MarkerCollector> collectors;
  
  public GraderBuilder() {
    findBugsCollector = new FindBugsMarkerCollector();
    
    collectors = new LinkedList<MarkerCollector>();
    collectors.add(findBugsCollector);
  }
  
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
	 *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
			throws CoreException {
		
	  IProject project = getProject();
	  for (MarkerCollector collector : collectors) {
	    collector.clearAllMarkers();
	    collector.addMarkers(project);
	  }
	  
	  //TODO extract information from collectors, update view(s)
	  
		return null;
	}

}
