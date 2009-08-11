package ie.ucd.autograder.metrics;

import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.grading.InputData;

import java.util.Map;

public class MetricsData extends AggregateData {

  public static final String NAME = "Metrics";
  
  public static final double METRICS_OVERALL_WEIGHT = 1;
  
  public static final double TLOC_WEIGHT = 0;
  public static final double METHOD_AVG_LOC_WEIGHT = 1;
  public static final double METHOD_AVG_CC_WEIGHT = 1;
  
  private double tloc;
  
  public MetricsData(Map<String,MetricHolder> metricsMap) {
    super(NAME);
    setData(metricsMap);
  }
  
  public final void setData(Map<String,MetricHolder> metricsMap) {
    clearInputData();
    // TLOC
    MetricHolder tlocMetric = metricsMap.get(MetricsConstants.TotalLinesOfCode.id);
    if (tlocMetric != null) {
      tloc = tlocMetric.getMetric();
      addInputData(new InputData("TLOC", Grade.getNALookup()).setMeasure(tloc), TLOC_WEIGHT);
    }
    
    // TLOC/Method
    MetricHolder mlocMetric = metricsMap.get(MetricsConstants.MethodLinesOfCode.id);
    if (mlocMetric != null) {
      addInputData(new InputData("Average method LOC", GradeLookupTable.METRICS_METHOD_LOC_LOOKUP).setMeasure(mlocMetric.getAvgPerMethod()), METHOD_AVG_LOC_WEIGHT);
    }
    
    // CC/Method
    MetricHolder ccMetric = metricsMap.get(MetricsConstants.McCabeCyclomaticComplexity.id);
    if (ccMetric != null) {
      addInputData(new InputData("Average method CC", GradeLookupTable.METRICS_METHOD_CC_LOOKUP).setMeasure(ccMetric.getAvgPerMethod()), METHOD_AVG_CC_WEIGHT);
    }
  }

  public double getTLOC() {
    return tloc;
  }
  
}
