package ie.ucd.autograder.builder;

import ie.ucd.autograder.builder.markercollectors.CheckstyleMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.ESCJava2MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.FindBugsMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.PMDMarkerCollector;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.metrics.MetricHolder;
import ie.ucd.autograder.metrics.MetricsConstants;
import ie.ucd.autograder.metrics.MetricsData;
import ie.ucd.autograder.metrics.MetricsConstants.IdName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import net.sourceforge.metrics.core.Avg;
import net.sourceforge.metrics.core.Constants;
import net.sourceforge.metrics.core.Max;
import net.sourceforge.metrics.core.Metric;
import net.sourceforge.metrics.core.sources.AbstractMetricSource;
import net.sourceforge.metrics.core.sources.Cache;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;

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

    IJavaProject javaProject = JavaCore.create(getProject());
    //Only operate on Java projects.
    if (javaProject != null) {
      for (MarkerCollector collector : collectors) {
        collector.clearAllMarkers();
        collector.addMarkers(project);
      }
      Map<String,MetricHolder> metricMap = metricsBuild(javaProject);
      
      storeProjectData(project, metricMap, collectors);
      
    } else {
      System.out.println("Not a java project");
      System.out.println(project.getClass());
    }
    //TODO extract information from collectors, update view(s)

    return null;
  }


  private void storeProjectData(IProject project, Map<String,MetricHolder> metricMap, List<MarkerCollector> collectors) {
    
    List<AggregateData> projectData = new ArrayList<AggregateData>(1 + collectors.size());
    
    MetricsData metrics = new MetricsData(metricMap);
    projectData.add(metrics);
    
    double tloc = metrics.getTLOC();
    double kloc = tloc / 1000d;
    for (MarkerCollector collector : collectors) {
      projectData.add(collector.getAggregateData(kloc));
    }    
    
    DataStore.getInstance(project).setDataForProject(project, projectData);
//    System.out.println("Data for project " + project);
//    System.out.println("Size: " + projectData.size());
//    for (AggregateData d : projectData) {
//      System.out.println(d);
//    }
  }
  

  private Map<String,MetricHolder> metricsBuild(IJavaProject project) {
    Cache cache = Cache.singleton;

    Map<String,MetricHolder> metricMap = new HashMap<String,MetricHolder>();
//        MetricsPlugin plugin = MetricsPlugin.getDefault();
//        String[] names = plugin.getMetricIds();
//        String[] descriptions = plugin.getMetricDescriptions();
//        System.out.println("Names: " + Arrays.asList(names));
//        System.out.println("Descriptions: " + Arrays.asList(descriptions));

    AbstractMetricSource ms = cache.get(project);
    for (IdName idName : MetricsConstants.METRICS) {
      String name = idName.id;
      Metric metric = ms.getValue(name);

      Avg averagePerPackage = ms.getAverage(name, Constants.PER_PACKAGE);        
      Max maxPerPackage = ms.getMaximum(name, Constants.PER_PACKAGE);
      Avg averagePerClass = ms.getAverage(name, Constants.PER_CLASS);
      Max maxPerClass = ms.getMaximum(name, Constants.PER_CLASS);
      Avg averagePerMethod = ms.getAverage(name, Constants.PER_METHOD);
      Max maxPerMethod = ms.getMaximum(name, Constants.PER_METHOD);
      MetricHolder holder = new MetricHolder(idName, metric, averagePerPackage, maxPerPackage, averagePerClass, maxPerClass, averagePerMethod, maxPerMethod);
      metricMap.put(name, holder);

    }
    return metricMap;
  }


}
