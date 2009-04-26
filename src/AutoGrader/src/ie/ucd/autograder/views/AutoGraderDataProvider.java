/**
 * 
 */
package ie.ucd.autograder.views;

import ie.ucd.autograder.builder.DataStore;
import ie.ucd.autograder.builder.GraderBuilder;
import ie.ucd.autograder.grading.AggregateData;
import ie.ucd.autograder.grading.InputData;
import ie.ucd.autograder.util.Pair;

import java.util.List;

import net.sourceforge.nattable.data.IColumnHeaderLabelProvider;
import net.sourceforge.nattable.data.IDataProvider;

import org.eclipse.core.resources.IProject;

public class AutoGraderDataProvider implements IDataProvider, IColumnHeaderLabelProvider {

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
    updateData();
  }

  public void updateData() {
    projectData = selectedProject == null ? null : DataStore.getInstance(selectedProject, true).getDataForProject(selectedProject);
    System.out.println("Data updated to");
    System.out.println(projectData);
  }

  public int getColumnCount() {
    if (selectedProject != null && projectData != null) {
      return projectData.size();
    } else {
      return 1;
    }
  }

  public int getRowCount() {
    numberOfRows = calculateRowCount();
    return numberOfRows;
  }

  public int calculateRowCount() {
    if (selectedProject != null && projectData != null) {

      int numRows = 0;
      for (AggregateData data : projectData) {
        int size = data.getData().size();
        size *= data.getName().equals(GraderBuilder.TOTAL_NAME) ? 2 : 3;
        if (size > numRows) {
          numRows = size;
        }
      }
      return numRows + 1; //Plus summary
    } else {
      return 1;
    }
  }

  public Object getValue(int row, int col) {
    if (selectedProject != null) {
      if (projectData != null) {

        //Get col data
        AggregateData data = col < projectData.size() ? projectData.get(col) : null;
        if (data != null) {
          if (row == numberOfRows - 1) {
            //Summary row
            return "Grade: " + data.getGrade();
          } else {
            List<Pair<InputData,Double>> subData = data.getData();
            //If totals
            if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
              if ((subData.size()*2) <= row) {
                return "";
              } else {
                int itemIndex = row/2;
                InputData iData = subData.get(itemIndex).getFirst();
                if (row % 2 == 0) {
                  //Input name
                  return iData.getName() + ":";
                } else {
                  //Grade
                  return "Grade: " + iData.getGrade();
                }
              }
            } else {
              //Normal column
              if ((subData.size()*3) <= row) {
                return "";
              } else {
                int itemIndex = row/3;
                InputData iData = subData.get(itemIndex).getFirst();
                if (row % 3 == 0) {
                  //Measure name
                  return iData.getName() + ":";
                } else if (row % 3 == 1){
                  //Measure
                  return iData.getMeasureAsString();
                } else {
                  //Grade
                  return "Grade: " + iData.getGrade();
                }
              }
            }       
          }
        } else {
          return "";
        }

      } else {
        return "No data for project " + selectedProject.getName();
      }
    } else {
      return "No data for selection.";
    }
  }

  public String getColumnHeaderLabel(int col) {
    if (selectedProject != null && projectData != null) {
      return projectData.get(col).getName();
    } else {
      return "";
    }
  }
  
  public boolean shouldShowColumnHeader() {
    return selectedProject != null && projectData != null;
  }
}