package ie.ucd.autograder.builder;

import ie.ucd.autograder.AutoGraderPlugin;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;
import ie.ucd.autograder.config.AGConfig;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.metrics.MetricHolder;
import ie.ucd.autograder.metrics.MetricsConstants;
import ie.ucd.autograder.metrics.MetricsConstants.IdName;
import ie.ucd.autograder.metrics.MetricsData;
import ie.ucd.autograder.util.Log;
import ie.ucd.autograder.views.AutoGraderView;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.sourceforge.metrics.builder.IMetricsProgressListener;
import net.sourceforge.metrics.builder.MetricsBuilder;
import net.sourceforge.metrics.core.Avg;
import net.sourceforge.metrics.core.Constants;
import net.sourceforge.metrics.core.Max;
import net.sourceforge.metrics.core.Metric;
import net.sourceforge.metrics.core.sources.AbstractMetricSource;
import net.sourceforge.metrics.core.sources.Cache;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jface.preference.IPreferenceStore;

public class GraderBuilder extends IncrementalProjectBuilder {

  /**
   * The timeout duration, for when we're waiting for Metrics to finish its 
   * work.
   */
  private static final int TIMEOUT = 2500; // 2.5 seconds
  
  public static final String BUILDER_ID = AutoGraderPlugin.PLUGIN_ID + ".builder";

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
    Log.info("Running AutoGrader builder on project " + project);
        
    List<AggregateData> projectData = collectProjectData(project);
    if (projectData != null) {
      DataStore.getInstance(project, false).setDataForProject(project, projectData);
      try {
        AutoGraderView view = AutoGraderView.getInstance();
        if (view != null) {
          view.update();
        }
      } catch (Exception e) {
        //Do nothing, view not initialised yet
      }
    }
    return new IProject[0];
  }
  
  public static List<AggregateData> collectProjectData(IProject project) throws CoreException {
    List<MarkerCollector> collectors = AGConfig.getMarkerCollectors(project);
    
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
      Log.info(project + " is not a java project: " + project.getClass());
      return null;
    }
  }

  public static final String TOTAL_NAME = "Total";
  
  private static List<AggregateData> createProjectData(IProject project, Map<String,MetricHolder> metricMap, List<MarkerCollector> collectors) {
    List<AggregateData> projectData = new ArrayList<AggregateData>(2 + collectors.size());
  
    GradeLookupTable mainTable = AGConfig.getMainGradeLookupTable(project);
    IPreferenceStore prefStore = AGConfig.getPreferenceStoreForProject(project);
    MetricsData metrics = new MetricsData(metricMap, project, mainTable);

    boolean metricsEnabled = prefStore.getBoolean(AutoGraderPlugin.PLUGIN_ID + ".collectors.metrics.enabled");
    if (metricsEnabled) {
      Log.info("Metrics are enabled");
      projectData.add(metrics);
    } else {
      Log.info("Metrics are not enabled");
    }
        
    double tloc = metrics.getTLOC();
    tloc = tloc == 0 ? 0.00000001 : tloc; //Avoid div0 errors, but small enough to show up as zero
    double kloc = tloc / 1000d;
    for (MarkerCollector collector : collectors) {
      projectData.add(collector.getAggregateData(kloc, mainTable));
    }
    
    AggregateData total = new AggregateData(TOTAL_NAME, mainTable, true);
    total.addInputData(projectData.get(0), metrics.getWeight());
    for (int i=0; i < collectors.size(); i++) {
      total.addInputData(projectData.get(i+(metricsEnabled?1:0)), collectors.get(i).getOverallWeight());
    }    
    projectData.add(total);
    
    return projectData;
  }
  

  private static Map<String,MetricHolder> metricsBuild(IJavaProject project) {
    Cache cache = Cache.singleton;
    Map<String,MetricHolder> metricMap = new HashMap<String,MetricHolder>();
    
    // if Metrics is busy, let's wait for it to finish
    if (MetricsBuilder.canAbort()) {
      MetricsBuilder.pause();
      final Object lock = new Object(); // the lock
      final MetricsListener ml = new MetricsListener(project, lock);
      MetricsBuilder.addMetricsProgressListener(ml);
      MetricsBuilder.resume();
      while (MetricsBuilder.canAbort()) {
        try {
          Log.info("Waiting for metrics...");
          synchronized (lock) {
            // wait for some amount of time; must time out because otherwise
            // there's a slight change of a race condition that would prevent us
            // from being notified
            lock.wait(TIMEOUT);
          }
        } catch (final InterruptedException e) {
          // if we're interrupted, we don't care
        }
      }
      MetricsBuilder.removeMetricsProgressListener(ml);
    }

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
      } else {
        Log.info("No metrics data in cache for project " + project);
      }
    } else {
      Log.info("No metrics cache available");
    }
    return metricMap;
  }

  /** 
   * A listener that performs a notification when a specified project is
   * completed.
   * 
   * @author Daniel M. Zimmerman
   */
  private static class MetricsListener implements IMetricsProgressListener
  {
    /**
     * The project.
     */
    private final IJavaProject my_project;
    
    /**
     * The lock to use for notification.
     */
    private final Object my_lock;
    
    /**
     * Constructs a new MetricsListener with the specified project and lock.
     * 
     * @param the_lock The lock.
     */
    public MetricsListener(final IJavaProject the_project, final Object the_lock) {
      my_project = the_project;
      my_lock = the_lock;
    }
    
    /**
     * {@inheritDoc}
     */
    public void completed(final IJavaElement the_element, final Object the_data) {}
    
    /**
     * {@inheritDoc}
     */
    public void moved(final IJavaElement the_element, final IPath the_path) {}
    
    /**
     * {@inheritDoc}
     */
    public void paused() {}
    
    /**
     * {@inheritDoc}
     */
    public void pending(final IJavaElement the_element) {}
    
    /**
     * Notifies the GraderBuilder when the project is complete, by using
     * notifyAll() on the lock.
     * 
     * @param the_project The project that is complete.
     * @param the_aborted_flag true if the metrics computation was aborted.
     */
    public void projectComplete(final IJavaProject the_project, 
                                final boolean the_aborted_flag) {
      if (the_project.equals(my_project)) {
        synchronized (my_lock) {
          my_lock.notifyAll();
        }
      }
    }
    
    /**
     * {@inheritDoc}
     */
    public void queued(final int the_count) {}
  }
}
