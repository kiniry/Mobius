package ie.ucd.autograder.views;

import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.views.AutoGraderDataProvider.GradeHolder;
import ie.ucd.autograder.views.AutoGraderDataProvider.MeasureString;
import ie.ucd.autograder.views.AutoGraderDataProvider.TitleString;
import net.sourceforge.nattable.typeconfig.style.DefaultStyleConfig;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;

public class AutoGraderStyleConfig extends DefaultStyleConfig {
  private static final long serialVersionUID = 8946047618955230840L;

  private final AutoGraderDataProvider dataProvider;
  
  public AutoGraderStyleConfig(AutoGraderDataProvider dataProvider) {
    this.dataProvider = dataProvider;
  }

  @Override
  public Color getBackgroundColor(int row, int col) {
    Object value = dataProvider.getValue(row, col);
    if (value instanceof GradeHolder) {
      return gradeToColour(((GradeHolder)value).grade);
    } else if (value instanceof TitleString) {
      return AutoGraderView.ENTRY_TITLE_COLOR;
    } else if (value instanceof MeasureString) {
      return AutoGraderView.MEASURE_COLOR;
    } else {
      return super.getBackgroundColor(row, col);
    }
  }

  @Override
  public Font getFont(int row, int col) {
    return super.getFont(row, col);
  }

  @Override
  public Color getForegroundColor(int row, int col) {
    return super.getForegroundColor(row, col);
  }

  @Override
  public Image getImage(int row, int col) {
    return super.getImage(row, col);
  }
  
  public static Color gradeToColour(Grade grade) {
    switch (grade) {
    case A_PLUS: 
    case A:
    case A_MINUS:
    case B_PLUS:
    case B:
      return AutoGraderView.GRADE_OK;
    case B_MINUS:
    case C_PLUS:
    case C:
    case C_MINUS:
      return AutoGraderView.GRADE_WARNING;
    case D_PLUS:
    case D:
    case D_MINUS:
    case E_PLUS:
    case E:
    case E_MINUS:
    case F_PLUS:
    case F:
    case F_MINUS:
    case G:
    case NG:
      return AutoGraderView.GRADE_ERROR;
    case NA:
      return AutoGraderView.EMPTY_COLOR;
    default:
      return AutoGraderView.GRADE_ERROR;
    }
  }
  
}
