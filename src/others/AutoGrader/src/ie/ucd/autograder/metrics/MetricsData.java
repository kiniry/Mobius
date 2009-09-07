package ie.ucd.autograder.metrics;

import ie.ucd.autograder.AutoGraderPlugin;
import ie.ucd.autograder.config.AGConfig;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.grading.InputData;

import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.preference.IPreferenceStore;

public class MetricsData extends AggregateData {

  public static final String NAME = "Metrics";

  public static final double TLOC_WEIGHT = 0;

  private double tloc;
  private float weight;

  public MetricsData(Map<String,MetricHolder> metricsMap, IProject project, GradeLookupTable table) {
    super(NAME, table, false);
    setData(metricsMap, project);
  }

  public final void setData(Map<String,MetricHolder> metricsMap, IProject project) {
    clearInputData();

    // TLOC
    MetricHolder tlocMetric = metricsMap.get(MetricsConstants.TotalLinesOfCode.id);
    if (tlocMetric != null) {
      tloc = tlocMetric.getMetric();
      addInputData(new InputData("TLOC", Grade.getNALookup()).setMeasure(tloc), TLOC_WEIGHT);
    }

    String id = AutoGraderPlugin.PLUGIN_ID + ".collectors.metrics.";
    IPreferenceStore store = AGConfig.getPreferenceStoreForProject(project);

    weight = store.getFloat(id + "overallweight");

    boolean mlocEnabled = store.getBoolean(id + "methodloc.enabled");
    if (mlocEnabled) {
      String mlocLookupString = store.getString(id + "methodloc.lookup");
      GradeLookupTable table = AGConfig.getGradeLookupTableFromPreferenceString(mlocLookupString);
      float mlocWeight = store.getFloat(id + "methodloc.weight");
      // TLOC/Method
      MetricHolder mlocMetric = metricsMap.get(MetricsConstants.MethodLinesOfCode.id);
      if (mlocMetric != null) {
        addInputData(new InputData("Average method LOC", table).setMeasure(mlocMetric.getAvgPerMethod()), mlocWeight);
      }
    }

    boolean mccEnabled = store.getBoolean(id + "methodcc.enabled");
    if (mccEnabled) {
      String mccLookupString = store.getString(id + "methodcc.lookup");
      GradeLookupTable table = AGConfig.getGradeLookupTableFromPreferenceString(mccLookupString);
      float mccWeight = store.getFloat(id + "methodcc.weight");
      //CC/Method
      MetricHolder ccMetric = metricsMap.get(MetricsConstants.McCabeCyclomaticComplexity.id);
      if (ccMetric != null) {
        addInputData(new InputData("Average method CC", table).setMeasure(ccMetric.getAvgPerMethod()), mccWeight);
      }
    }
  }

  public double getTLOC() {
    return tloc;
  }

  public float getWeight() {
    return weight;
  }

}
