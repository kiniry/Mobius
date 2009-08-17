/**
 * 
 */
package ie.ucd.autograder.views;

import ie.ucd.autograder.builder.DataStore;
import ie.ucd.autograder.builder.GraderBuilder;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.grading.InputData;
import ie.ucd.autograder.util.Pair;

import java.util.List;

import org.eclipse.core.resources.IProject;

public class AutoGraderDataProvider {

  private IProject selectedProject;
  private List<AggregateData> projectData;
  private int numberOfRows;

  private AutoGraderDataProvider() {}

  private static final AutoGraderDataProvider instance = new AutoGraderDataProvider();
  public static AutoGraderDataProvider getInstance() {
    return instance;
  }

  public void setSelectedProject(IProject project) {
    selectedProject = project;
    numberOfRows = 1;
    updateData();
  }

  public void updateData() {
    projectData = selectedProject == null ? null : DataStore.getInstance(selectedProject, true).getDataForProject(selectedProject);
    //System.out.println("Updated data. Project data: " + projectData);
    //System.out.println("selectedProject: " + selectedProject);
    updateRowCount();
  }

  public int getColumnCount() {
    return (selectedProject != null && projectData != null) ? projectData.size() : 1;
  }

  public int getBodyRowCount() {
    return (selectedProject != null && projectData != null) ? numberOfRows : 1;
  }

  public void updateRowCount() {
    if (selectedProject != null && projectData != null) {
      int numRows = 0;
      for (AggregateData data : projectData) {
        if (data.getName().equals(GraderBuilder.TOTAL_NAME)) continue;
        int size = data.getData().size();
        size *= 3;
        if (size > numRows) {
          numRows = size;
        }
      }
      numberOfRows = numRows + 2; //Plus summary 
    } else {
      numberOfRows = 1;
    }
  }

  public Object getColumnHeader(int columnIndex) {
    if (selectedProject == null || projectData == null) {
      return new TitleString(""); 
    }
    AggregateData data = columnIndex < projectData.size() ? projectData.get(columnIndex) : null;
    if (data == null) {
      return new TitleString("");
    } else {
      return new TitleString(data.getName());
    }
  }
  
  //TODO cache results, clear cache after change in data...
  public Object getBodyDataValue(int row, int col) {
    if (selectedProject != null) {
      if (projectData != null) {

        //Get col data
        AggregateData data = col < projectData.size() ? projectData.get(col) : null;
        if (data != null) {
          if (row == numberOfRows - 2) {
            if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
              return new TitleString("Overall");
            } else {
              return new TitleString("Total");
            }
          } else if (row == numberOfRows - 1) {
            //Summary row
            if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
              return new OverallGrade(data.getGrade());
            } else {
              return new ItemGrade(data.getGrade());
            }
          } else {
            List<Pair<InputData,Double>> subData = data.getData();
            //If totals
            if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
//              if ((subData.size()*2) <= row) {
//                return "";
//              } else {
//                int itemIndex = row/2;
//                InputData iData = subData.get(itemIndex).getFirst();
//                if (row % 2 == 0) {
//                  //Input name
//                  return new TitleString(iData.getName());
//                } else {
//                  //Grade
//                  return new SubGrade(iData.getGrade());
//                }
//              }
              return "";
            } else {
              //Normal column
              if ((subData.size()*3) <= row) {
                return "";
              } else {
                int itemIndex = row/3;
                InputData iData = subData.get(itemIndex).getFirst();
                if (row % 3 == 0) {
                  //Measure name
                  return new TitleString(iData.getName());
                } else if (row % 3 == 1){
                  //Measure
                  return new MeasureString(iData.getMeasureAsString());
                } else {
                  //Grade
                  return new SubGrade(iData.getGrade());
                }
              }
            }       
          }
        } else {
          return "";
        }

      } else {
        return "No data for " + selectedProject.getName();
      }
    } else {
      return "No data for selection.";
    }
  }
 
  public static class StringHolder {
    public final String string;
    public StringHolder(String string) { this.string = string; }
    public String toString() { return string; }
  }
  
  public static class TitleString extends StringHolder {
    public TitleString(String string) { super(string); }
    public String toString() { return string + ":"; }
  }
  
  public static class MeasureString extends StringHolder {
    public MeasureString(String string) { super(string); }
  }
  
  public static class GradeHolder {
    public final Grade grade;
    public GradeHolder(Grade g) { grade = g; }
    public String toString() { return "Grade: " + grade; }
  }
  
  public static class ItemGrade extends GradeHolder {
    public ItemGrade(Grade g) { super(g); }
  }
  
  public static class OverallGrade extends GradeHolder {
    public OverallGrade(Grade g) { super(g); }
  }
  
  public static class SubGrade extends GradeHolder {
    public SubGrade(Grade g) { super(g); }
  }
}