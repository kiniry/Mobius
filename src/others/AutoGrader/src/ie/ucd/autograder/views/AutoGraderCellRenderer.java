package ie.ucd.autograder.views;

import ie.ucd.autograder.views.AutoGraderDataProvider.GradeHolder;
import ie.ucd.autograder.views.AutoGraderDataProvider.MeasureString;
import ie.ucd.autograder.views.AutoGraderDataProvider.TitleString;

public class AutoGraderCellRenderer 
//extends DataBindingCellRenderer 
{

  private AutoGraderStyleConfig style;
  
  public AutoGraderCellRenderer(AutoGraderDataProvider dataProvider) {
    //super(dataProvider);
    style = new AutoGraderStyleConfig(dataProvider);
  }

//  @Override
  public String getDisplayText(int row, int col) {
    Object value = null; //getValue(row, col);
    if (value instanceof GradeHolder) {
      return "Grade: " + ((GradeHolder)value).grade;
    } else if (value instanceof TitleString) {
      return ((TitleString)value).string + ":";
    } else if (value instanceof MeasureString) {
      return ((MeasureString)value).string;
    } else {
      return value.toString();
    }
  }

//  @Override
//  public IStyleConfig getStyleConfig(String displayMode, int row, int col) {
//    return style;
//  }

}
