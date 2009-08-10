package ie.ucd.autograder.builder;

import ie.ucd.autograder.grading.AggregateData;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;

public final class DataStore {

  private static DataStore instance;
  public static DataStore getInstance(IProject aProject, boolean includeThisProject) {
    if (instance == null) {
      instance = new DataStore();
      
      //As a slightly ugly way of 
      IProject[] projects = aProject.getWorkspace().getRoot().getProjects();
      for (IProject project : projects) {
        if (includeThisProject || project != aProject) {
          try {
            if (project.hasNature(GraderNature.NATURE_ID)) {
              List<AggregateData> projectData = GraderBuilder.collectProjectData(project, GraderBuilder.createCollectors());
              if (projectData != null) {
                instance.setDataForProject(project, projectData);
              }
            }
          } catch (CoreException e) {
            //Do nothing
          }
        }
      }      
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
