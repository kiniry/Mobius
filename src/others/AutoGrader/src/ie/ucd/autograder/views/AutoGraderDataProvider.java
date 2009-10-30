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

import java.util.ArrayList;
import java.util.List;

import net.sourceforge.nattable.layer.LabelStack;
import net.sourceforge.nattable.layer.cell.IConfigLabelAccumulator;

import org.eclipse.core.resources.IProject;

public class AutoGraderDataProvider implements IConfigLabelAccumulator {

  private IProject selectedProject;
  private List<AggregateData> projectData;
  private int numberOfRows;

  Object[][] cellData;

  private AutoGraderDataProvider() {}

  private static final AutoGraderDataProvider instance = new AutoGraderDataProvider();
  public static AutoGraderDataProvider getInstance() {
    return instance;
  }

  public void setSelectedProject(IProject project) {
    //    System.out.println("Changed selected project to " + project);
    selectedProject = project;
    numberOfRows = 1;
    updateData();
  }

  public void updateData() {
    projectData = selectedProject == null ? null : DataStore.getInstance(selectedProject, true).getDataForProject(selectedProject);
    //    System.out.println("Updated data. Project data: " + projectData);
    //    System.out.println("selectedProject: " + selectedProject);
    updateRowCount();

    if (selectedProject != null && projectData != null) {
      cellData = new Object[numberOfRows][projectData.size()];
      for (int i=0; i < cellData.length; i++) {
        for (int j=0; j < cellData[0].length; j++) {
          cellData[i][j] = internalBodyDataValue(i, j);
        }
      }
    }
  }

  public boolean validData() {
    return selectedProject != null && projectData != null;
  }

  public int getColumnCount() {
    return validData() ? projectData.size() : 1;
  }

  public int getBodyRowCount() {
    return validData() ? numberOfRows : 1;
  }

  public void updateRowCount() {
    if (validData()) {
      int numRows = 0;
      for (AggregateData data : projectData) {
        int size = 0;
        if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
          //size = data.getData().size() * 2;

        } else {
          size = data.getData().size() * 3;
        }
        if (size > numRows) {
          numRows = size;
        }
      }
      numberOfRows = numRows + 3; //Plus spacer and summary 
    } else {
      numberOfRows = 1;
    }
  }

  public Object getColumnHeader(int columnIndex) {
    if (!validData()) {
      return BlankCellData.instance; 
    }
    AggregateData data = columnIndex < projectData.size() ? projectData.get(columnIndex) : null;
    if (data == null) {
      return new ColumnHeaderString("");
    } else {
      return new ColumnHeaderString(data.getName());
    }
  }

  public Object getBodyDataValue(int row, int col) {
    if (selectedProject != null) {
      if (projectData != null && cellData != null) {
        if (row > cellData.length-1 || col > cellData[0].length) {
          return "An error occurred.";
        } else {
          return cellData[row][col];
        }        
      } else {
        return "No data for " + selectedProject.getName() + ". Is the AutoGrader nature enabled for this project?";
      }
    } else {
      return "No data for selection. Please select an AutoGrader-enabled project from the Package Explorer or Project Explorer.";
    }
  }

  private Object internalBodyDataValue(int row, int col) {
    if (selectedProject != null) {
      if (projectData != null) {
        //Get column in question
        AggregateData data = col < projectData.size() ? projectData.get(col) : null;
        if (data != null) {
          return internalGetBodyDataValue(data, row, col);
        } else {
          return BlankCellData.instance;
        }
      } else {
        return "No data for " + selectedProject.getName();
      }
    } else {
      return "No data for selection.";
    }
  }

  private Object internalGetBodyDataValue(AggregateData data, int row, int col) {
    if (row == numberOfRows - 2) {
      if (data.getName().equals(GraderBuilder.TOTAL_NAME)) {
        return OverallTitleString.instance;
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
        return getTotalColumnCell(subData, row, col);
      } else {
        //Normal column
        return getNormalColumnCell(subData, row, col);
      }       
    }
  }

  private Object getTotalColumnCell(List<Pair<InputData,Double>> subData, int row, int col) {
    //    if ((subData.size()*2) <= row) {
    //      return "";
    //    } else {
    //      int itemIndex = row/2;
    //      InputData iData = subData.get(itemIndex).getFirst();
    //      if (row % 2 == 0) {
    //        //Input name
    //        return new TitleString(iData.getName());
    //      } else {
    //        //Grade
    //        return new SubGrade(iData.getGrade());
    //      }
    //    }
    return BlankCellData.instance;
  }

  private Object getNormalColumnCell(List<Pair<InputData,Double>> subData, int row, int col) {
    if ((subData.size()*3) <= row) {
      return BlankCellData.instance;
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

  public void accumulateConfigLabels(LabelStack configLabels, int columnPosition, int rowPosition) {
    //    System.out.println("Labels for (" + columnPosition + "," + rowPosition + ")");
    if (cellData != null && rowPosition < cellData.length && columnPosition < cellData[0].length) {
      Object cell = cellData[rowPosition][columnPosition];
      if (cell instanceof CellData) {
        //        System.out.println("(" + columnPosition + "," + rowPosition + ") is a CellData, class: " + cell.getClass());
        for (String label : ((CellData)cell).getLabels()) {
          //          System.out.println("Adding label " + label);
          configLabels.addLabel(label);
        }
      }
    }
  }

  public static abstract class CellData {
    public abstract List<String> getLabels();
  }

  public static class BlankCellData {
    public static final String BLANK_CELL = "BLANK_CELL";
    private static final BlankCellData instance = new BlankCellData();
    private List<String> labels;
    public List<String> getLabels() { 
      if (labels == null) {
        labels = new ArrayList<String>();
        labels.add(BLANK_CELL);
      }
      return labels;
    }
    public String toString() { return ""; }
  }

  public static class StringHolder extends CellData {
    public static final String STRING_CELL = "STRING_CELL";

    public final String string;
    public StringHolder(String string) { this.string = string; }
    public String toString() { return string; }

    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = new ArrayList<String>();
        labels.add(STRING_CELL);
      }
      return labels;
    }
  }
  
  public static class NoDataStringHolder extends StringHolder {
    public static final String NO_DATA_CELL = "NO_DATA_CELL";
    public NoDataStringHolder(String string) { super(string); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(NO_DATA_CELL);
      }
      return labels;
    }
  }
  
  public static class ErrorStringHolder extends StringHolder {
    public static final String ERROR_CELL = "ERROR_CELL";
    public ErrorStringHolder(String string) { super(string); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(ERROR_CELL);
      }
      return labels;
    }
  }

  public static class ColumnHeaderString extends StringHolder {
    public static final String COLUMN_HEADER = "COLUMN_HEADER";

    public ColumnHeaderString(String string) { super(string); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(COLUMN_HEADER);
      }
      return labels;
    }
  }

  public static class TitleString extends StringHolder {
    public static final String TITLE_CELL = "TITLE_CELL";
    public TitleString(String string) { super(string); }
    public String toString() { return string + ":"; }

    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(TITLE_CELL);
      }
      return labels;
    }
  }
  
  public static class OverallTitleString extends TitleString {
    public static final String OVERALL_TITLE_CELL = "OVERALL_TITLE_CELL";
    public static OverallTitleString instance = new OverallTitleString("Overall");
    private OverallTitleString(String string) { super(string); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(OVERALL_TITLE_CELL);
      }
      return labels;
    }
  }

  public static class MeasureString extends StringHolder {
    public static final String MEASURE_CELL = "MEASURE_CELL";
    public MeasureString(String string) { super(string); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(MEASURE_CELL);
      }
      return labels;
    }
  }

  public static class GradeHolder extends CellData {
    public static final String GRADE_CELL = "GRADE_CELL";
    public static final String GRADE = "GRADE_";
    public final Grade grade;
    public GradeHolder(Grade g) { grade = g; }
    public String toString() { return "Grade: " + grade; }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = new ArrayList<String>();
        labels.add(GRADE_CELL);
        labels.add(GRADE + grade);
      }
      return labels;
    }
  }

  public static class ItemGrade extends GradeHolder {
    public static final String ITEM_GRADE_CELL = "ITEM_GRADE_CELL";
    public ItemGrade(Grade g) { super(g); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(ITEM_GRADE_CELL);
      }
      return labels;
    }
  }

  public static class OverallGrade extends GradeHolder {
    public static final String OVERALL_GRADE_CELL = "OVERALL_GRADE_CELL";
    public OverallGrade(Grade g) { super(g); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(OVERALL_GRADE_CELL);
      }
      return labels;
    }
  }

  public static class SubGrade extends GradeHolder {
    public static final String SUB_GRADE_CELL = "SUB_GRADE_CELL";
    public SubGrade(Grade g) { super(g); }
    private List<String> labels;
    public List<String> getLabels() {
      if (labels == null) {
        labels = super.getLabels();
        labels.add(SUB_GRADE_CELL);
      }
      return labels;
    }
  }
}