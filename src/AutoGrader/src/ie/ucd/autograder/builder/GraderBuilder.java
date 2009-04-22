package ie.ucd.autograder.builder;

import ie.ucd.autograder.builder.markercollectors.CheckstyleMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.ESCJava2MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.FindBugsMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.PMDMarkerCollector;

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
  private final PMDMarkerCollector pmdMarkerCollector;
  private final CheckstyleMarkerCollector checkstyleMarkerCollector;
  private final ESCJava2MarkerCollector escMarkerCollector;
  private final List<MarkerCollector> collectors;
  
  public GraderBuilder() {
    findBugsCollector = new FindBugsMarkerCollector();
    pmdMarkerCollector = new PMDMarkerCollector();
    checkstyleMarkerCollector = new CheckstyleMarkerCollector();
    escMarkerCollector = new ESCJava2MarkerCollector();
    
    collectors = new LinkedList<MarkerCollector>();
    collectors.add(findBugsCollector);
    collectors.add(pmdMarkerCollector);
    collectors.add(checkstyleMarkerCollector);
    collectors.add(escMarkerCollector);
  }
  
	/*
	 * (non-Javadoc)
	 * 
	 * @see org.eclipse.core.internal.events.InternalBuilder#build(int,
	 *      java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
	 */
	@SuppressWarnings("unchecked")
  protected IProject[] build(int kind, Map args, IProgressMonitor monitor)
			throws CoreException {
		
	  System.out.println("Running builder");
	  
	  IProject project = getProject();
	  for (MarkerCollector collector : collectors) {
	    collector.clearAllMarkers();
	    collector.addMarkers(project);
	  }
	  
	  //TODO extract information from collectors, update view(s)
	  
		return null;
	}

}
