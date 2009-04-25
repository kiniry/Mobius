package ie.ucd.autograder.metrics;

import ie.ucd.autograder.metrics.MetricsConstants.IdName;
import net.sourceforge.metrics.core.Avg;
import net.sourceforge.metrics.core.Max;
import net.sourceforge.metrics.core.Metric;

public class MetricHolder {

  private final IdName idName;
  private final Metric metric;
  private final Avg avgPerPackage;
  private final Max maxPerPackage;
  private final Avg avgPerClass;
  private final Max maxPerClass;
  private final Avg avgPerMethod;
  private final Max maxPerMethod;
  
  public MetricHolder(IdName idName, Metric metric, Avg avgPerPackage, Max maxPerPackage,
      Avg avgPerClass, Max maxPerClass, Avg avgPerMethod, Max maxPerMethod) {
    this.idName = idName;
    this.metric = metric;
    this.avgPerPackage = avgPerPackage;
    this.maxPerPackage = maxPerPackage;
    this.avgPerClass = avgPerClass;
    this.maxPerClass = maxPerClass;
    this.avgPerMethod = avgPerMethod;
    this.maxPerMethod = maxPerMethod;
  }

  public double getMetric() {
    return metric.doubleValue();
  }

  public double getAvgPerPackage() {
    return avgPerPackage.doubleValue();
  }

  public double getMaxPerPackage() {
    return maxPerPackage.doubleValue();
  }

  public double getAvgPerClass() {
    return avgPerClass.doubleValue();
  }

  public double getMaxPerClass() {
    return maxPerClass.doubleValue();
  }

  public double getAvgPerMethod() {
    return avgPerMethod.doubleValue();
  }

  public double getMaxPerMethod() {
    return maxPerMethod.doubleValue();
  }  
  
  public String getMetricId() {
    return idName.id;
  }
  
  public String getMetricName() {
    return idName.name;
  }
}
