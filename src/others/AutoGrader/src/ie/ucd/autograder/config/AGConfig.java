package ie.ucd.autograder.config;

import ie.ucd.autograder.AutoGraderPlugin;
import ie.ucd.autograder.builder.markercollectors.MarkerCollector;
import ie.ucd.autograder.config.ui.ProjectConfigurationPropertyPage;
import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.grading.GradeLookupTable;
import ie.ucd.autograder.util.Pair.MarkGradePair;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;
import java.util.Map.Entry;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.ProjectScope;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.ui.preferences.ScopedPreferenceStore;

public class AGConfig {

  public static GradeLookupTable getMainGradeLookupTable(IProject project) {
    IPreferenceStore store = getPreferenceStoreForProject(project);
    List<MarkGradePair> pairs = new ArrayList<MarkGradePair>();
    String id = AutoGraderPlugin.PLUGIN_ID + ".gradeboundaries.";
    
    for (Grade grade : Grade.values()) {
      boolean enabled = store.getBoolean(id + grade.name() + ".enabled");
      if (enabled) {
        Float value = store.getFloat(id + grade.name() + ".value");
        pairs.add(new MarkGradePair(value.doubleValue(), grade)); 
      }
    }
    return new GradeLookupTable(pairs);
  }
  
  public static List<MarkerCollector> getMarkerCollectors(IProject project) {
    List<MarkerCollector> collectors = new ArrayList<MarkerCollector>();
    IPreferenceStore store = getPreferenceStoreForProject(project);
    
    String gradersList = store.getString(AutoGraderPlugin.PLUGIN_ID + ".collectors");
    for (String graderId : gradersList.split(",")) {
      MarkerCollector collector = getMarkerCollector(store, graderId);
      if (collector != null) {
        collectors.add(collector);
      }
    }
    
    return collectors;
  }
  
  private static MarkerCollector getMarkerCollector(IPreferenceStore store, String graderId) {
    String id = AutoGraderPlugin.PLUGIN_ID + ".collectors." + graderId + '.';
    
    boolean enabled = store.getBoolean(id + "enabled");
    if (enabled) {
      
      String name = store.getString(id + "displayname");
      float weight = store.getFloat(id + "overallweight");
      String markerIdsString = store.getString(id + "markerids");
      List<String> markerIds = Arrays.asList(markerIdsString.split(","));
      boolean divKLoc = store.getBoolean(id + "divkloc");
      
      boolean errorsEnabled = store.getBoolean(id + "errorsenabled");
      float errorsWeight = store.getFloat(id + "errorsweight");
      String errorsLookupString = store.getString(id + "errorslookup");
      GradeLookupTable errorsLookup = getGradeLookupTableFromPreferenceString(errorsLookupString);
      
      boolean warningsEnabled = store.getBoolean(id + "warningsenabled");
      float warningsWeight = store.getFloat(id + "warningsweight");
      String warningsLookupString = store.getString(id + "warningslookup");
      GradeLookupTable warningsLookup = getGradeLookupTableFromPreferenceString(warningsLookupString);
      
      return new MarkerCollector(name, markerIds, weight, divKLoc, errorsEnabled, errorsWeight, errorsLookup, warningsEnabled, warningsWeight, warningsLookup);
    }
    
    return null;
  }
  
  public static GradeLookupTable getGradeLookupTableFromPreferenceString(String pref) {
    String[] parts = pref.split(";");
    
    List<MarkGradePair> lookupEntries = new ArrayList<MarkGradePair>();
    for (String part : parts) {
      String[] bits = part.split(",");
      if (bits.length == 2) {
        Grade grade = Grade.gradeFromStringName(bits[0]);
        Double mark = Double.parseDouble(bits[1]);
        lookupEntries.add(new MarkGradePair(mark, grade));
      } else {
        //TODO error, fail, ...?
      }
    }
    
    return new GradeLookupTable(lookupEntries);
  }
 
  private static Properties ucdProperties;
  private static Properties getUCDProperties() {
    if (ucdProperties == null) {
      ucdProperties = new Properties();
      try {
        ucdProperties.load(ProjectConfigurationPropertyPage.class.getResourceAsStream("/ie/ucd/autograder/config/ucd-config.properties"));
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
    return ucdProperties;
  }
  
  public static void initialiseDefaults(IPreferenceStore store) {
    Properties properties = getUCDProperties();
    for (Entry<Object,Object> entry : properties.entrySet()) {
      store.setDefault(entry.getKey().toString(), entry.getValue().toString());
    }
  }
  
  private static Map<IProject,IPreferenceStore> storeMap = new HashMap<IProject,IPreferenceStore>();
  public static IPreferenceStore getPreferenceStoreForProject(IProject project) {
    IPreferenceStore store = storeMap.get(project);
    if (store == null) {
      store = new ScopedPreferenceStore(new ProjectScope(project), AutoGraderPlugin.PLUGIN_ID);
      initialiseDefaults(store);
      storeMap.put(project, store);
    }
    return store;
  }
  
}
