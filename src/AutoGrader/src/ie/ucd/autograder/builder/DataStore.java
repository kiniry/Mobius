package ie.ucd.autograder.builder;

import ie.ucd.autograder.grading.AggregateData;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;

public class DataStore {

  private static DataStore instance;
  public static DataStore getInstance(IProject aProject) {
    if (instance == null) {
      aProject.getWorkspace().getRoot().getProjects();
      //TODO process these projects...
      instance = new DataStore();
    }
    return instance;
  }
  
  private final Map<IProject,List<AggregateData>> projectDataMap;
  
  private DataStore() {
    projectDataMap = new HashMap<IProject,List<AggregateData>>();
    
  }
  
  public List<AggregateData> getDataForProject(IProject project) {
    return projectDataMap.get(project);
  }
  
  public void setDataForProject(IProject project, List<AggregateData> data) {
    projectDataMap.put(project, data);
  }
}
