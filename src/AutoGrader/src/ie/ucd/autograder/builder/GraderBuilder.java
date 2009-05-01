package ie.ucd.autograder.builder;

import ie.ucd.autograder.builder.markercollectors.BONcMarkerCollector;
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
import ie.ucd.autograder.views.AutoGraderView;

import java.util.ArrayList;
import java.util.HashMap;
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
  private final List<MarkerCollector> collectors;

  public GraderBuilder() {
    collectors = createCollectors();
  }
  
  public static List<MarkerCollector> createCollectors() {
    List<MarkerCollector> collectors = new ArrayList<MarkerCollector>(4);
    collectors.add(new BONcMarkerCollector());
    collectors.add(new FindBugsMarkerCollector());
    collectors.add(new PMDMarkerCollector());
    collectors.add(new CheckstyleMarkerCollector());
    collectors.add(new ESCJava2MarkerCollector());
    return collectors;
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
    IProject project = getProject();
    List<AggregateData> projectData = collectProjectData(project, collectors);
    if (projectData != null) {
      DataStore.getInstance(project, false).setDataForProject(project, projectData);
      AutoGraderView view = AutoGraderView.getInstance();
      if (view != null) {
        view.update();
      }
    }
    return new IProject[0];
  }
  
  public static List<AggregateData> collectProjectData(IProject project, List<MarkerCollector> collectors) throws CoreException {
    IJavaProject javaProject = JavaCore.create(project);
    //Only operate on Java projects.
    if (javaProject != null) {
      for (MarkerCollector collector : collectors) {
        collector.clearAllMarkers();
        collector.addMarkers(project);
      }
      Map<String,MetricHolder> metricMap = metricsBuild(javaProject);
      
      return createProjectData(project, metricMap, collectors);
      
    } else {
      System.out.println("Not a java project");
      System.out.println(project.getClass());
      return null;
    }
  }

  public static final String TOTAL_NAME = "Total";
  
  private static List<AggregateData> createProjectData(IProject project, Map<String,MetricHolder> metricMap, List<MarkerCollector> collectors) {
    List<AggregateData> projectData = new ArrayList<AggregateData>(2 + collectors.size());
  
    MetricsData metrics = new MetricsData(metricMap);
    projectData.add(metrics);
    
    double tloc = metrics.getTLOC();
    tloc = tloc == 0 ? 0.00000001 : tloc; //Avoid div0 errors, but small enough to show up as zero
    double kloc = tloc / 1000d;
    for (MarkerCollector collector : collectors) {
      projectData.add(collector.getAggregateData(kloc));
    }
    
    AggregateData total = new AggregateData(TOTAL_NAME);
    total.addInputData(projectData.get(0), MetricsData.METRICS_OVERALL_WEIGHT);
    for (int i=0; i < collectors.size(); i++) {
      total.addInputData(projectData.get(i+1), collectors.get(i).getOverallWeight());
    }    
    projectData.add(total);
    
    return projectData;
  }
  

  private static Map<String,MetricHolder> metricsBuild(IJavaProject project) {
    Cache cache = Cache.singleton;

    Map<String,MetricHolder> metricMap = new HashMap<String,MetricHolder>();

    if (cache != null) {
      AbstractMetricSource ms = cache.get(project);
      if (ms != null) {
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
      }
    }
    return metricMap;
  }


}
