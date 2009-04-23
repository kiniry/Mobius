package ie.ucd.autograder.grading;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;

public class GradeStore {

  private static final GradeStore instance = new GradeStore();
  public static GradeStore getInstance() {
    return instance;
  }
  
  private final Map<IProject,List<InputData>> projectDataMap;
  
  private GradeStore() {
    projectDataMap = new HashMap<IProject,List<InputData>>();
  }
  
  public List<InputData> getDataForProject(IProject project) {
    return projectDataMap.get(project);
  }
  
  public void setDataForProject(IProject project, List<InputData> data) {
    projectDataMap.put(project, data);
  }
}
