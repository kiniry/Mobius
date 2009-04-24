package ie.ucd.autograder.builder;

import ie.ucd.autograder.builder.markercollectors.CheckstyleMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.ESCJava2MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.FindBugsMarkerCollector;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;
import ie.ucd.autograder.builder.markercollectors.PMDMarkerCollector;
import ie.ucd.autograder.metrics.MetricsConstants;
import ie.ucd.autograder.metrics.MetricsConstants.IdName;

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
      metricsBuild(javaProject);
    } else {
      System.out.println("Not a java project");
      System.out.println(project.getClass());
    }
    //TODO extract information from collectors, update view(s)

    return null;
  }



  private void metricsBuild(IJavaProject project) {
    System.out.println("Here...");
    Cache cache = Cache.singleton;

    //    MetricsPlugin plugin = MetricsPlugin.getDefault();
    //    String[] names = plugin.getMetricIds();
    //    String[] descriptions = plugin.getMetricDescriptions();
    //    System.out.println("Names: " + Arrays.asList(names));
    //    System.out.println("Descriptions: " + Arrays.asList(descriptions));

    AbstractMetricSource ms = cache.get(project);
    for (IdName idName : MetricsConstants.METRICS) {

      String name = idName.id;
      String description = idName.name;
      Metric metric = ms.getValue(name);

      if (metric != null) {
        double value = metric.getValue();
        
        System.out.println(name + ", " + description + "= " + value);
        
        /*
        Avg averagePerPackage = ms.getAverage(name, Constants.PER_PACKAGE);
        
        double averagePerPackageValue = averagePerPackage.doubleValue();
        double averagePerPackageStdDev = averagePerPackage.getStandardDeviation();
        Max maxPerPackage = ms.getMaximum(name, Constants.PER_PACKAGE);
        double maxPerPackageValue = maxPerPackage.doubleValue();

        Avg averagePerClass = ms.getAverage(name, Constants.PER_CLASS);
        double averagePerClassValue = averagePerClass.doubleValue();
        double averagePerClassStdDev = averagePerClass.getStandardDeviation();
        Max maxPerClass = ms.getMaximum(name, Constants.PER_CLASS);
        double maxPerClassValue = maxPerClass.doubleValue();

        Avg averagePerMethod = ms.getAverage(name, Constants.PER_METHOD);
        double averagePerMethodValue = averagePerMethod.doubleValue();
        double averagePerMethodStdDev = averagePerMethod.getStandardDeviation();
        Max maxPerMethod = ms.getMaximum(name, Constants.PER_METHOD);
        double maxPerMethodValue = maxPerMethod.doubleValue();
        */      
        }

    }
  }


}
