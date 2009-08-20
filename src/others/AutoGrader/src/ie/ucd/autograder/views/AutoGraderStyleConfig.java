package ie.ucd.autograder.views;

import ie.ucd.autograder.grading.Grade;
import net.sourceforge.nattable.config.AbstractRegistryConfiguration;
import net.sourceforge.nattable.config.CellConfigAttributes;
import net.sourceforge.nattable.config.ConfigRegistry;
import net.sourceforge.nattable.config.IConfigRegistry;
import net.sourceforge.nattable.data.convert.DefaultDisplayConverter;
import net.sourceforge.nattable.painter.cell.TextPainter;
import net.sourceforge.nattable.painter.cell.decorator.PaddingDecorator;
import net.sourceforge.nattable.style.BorderStyle;
import net.sourceforge.nattable.style.CellStyleAttributes;
import net.sourceforge.nattable.style.DisplayMode;
import net.sourceforge.nattable.style.HorizontalAlignmentEnum;
import net.sourceforge.nattable.style.Style;
import net.sourceforge.nattable.style.VerticalAlignmentEnum;
import net.sourceforge.nattable.util.GUIHelper;

import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

public class AutoGraderStyleConfig extends AbstractRegistryConfiguration {

  private static final HorizontalAlignmentEnum hAlign = HorizontalAlignmentEnum.CENTER;
  private static final VerticalAlignmentEnum vAlign = VerticalAlignmentEnum.MIDDLE;
  private static final BorderStyle borderStyle = null;  
  private static final Font font = GUIHelper.DEFAULT_FONT;

  public void configureRegistry(ConfigRegistry configRegistry) {
    applyBlankStylings(configRegistry);
    applyTitleStylings(configRegistry);
    applyMeasureStylings(configRegistry);
    applyGradeStylings(configRegistry);
    applyBasicStylings(configRegistry);    
    //applyColumnHeaderStylings(configRegistry);
    applyFontStylings(configRegistry);
  }
  
  private static void applyColumnHeaderStylings(IConfigRegistry config) {
    Style columnHeaderStyle = new Style();
    columnHeaderStyle.setAttributeValue(CellStyleAttributes.FONT, Fonts.BOLD_FONT);
    columnHeaderStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, GUIHelper.COLOR_WIDGET_BACKGROUND);
    //columnHeaderStyle.setAttributeValue(CellStyleAttributes.BORDER_STYLE, ...);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, columnHeaderStyle, DisplayMode.NORMAL, AutoGraderDataProvider.ColumnHeaderString.COLUMN_HEADER);
  }
  
  private static void applyFontStylings(IConfigRegistry config) {
    Style boldStyle = new Style();
    boldStyle.setAttributeValue(CellStyleAttributes.FONT, Fonts.BOLD_FONT);
    
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, boldStyle, DisplayMode.NORMAL, AutoGraderDataProvider.OverallTitleString.OVERALL_TITLE_CELL);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, boldStyle, DisplayMode.NORMAL, AutoGraderDataProvider.OverallGrade.OVERALL_GRADE_CELL);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, boldStyle, DisplayMode.NORMAL, AutoGraderDataProvider.ItemGrade.ITEM_GRADE_CELL);
  }

  private static void applyTitleStylings(IConfigRegistry config) {
    Style titleStyle = new Style();
    titleStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.ENTRY_TITLE_COLOR);

    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, titleStyle, DisplayMode.NORMAL, AutoGraderDataProvider.TitleString.TITLE_CELL);
  }

  private static void applyMeasureStylings(IConfigRegistry config) {
    Style measureStyle = new Style();
    measureStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.MEASURE_COLOR);

    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, measureStyle, DisplayMode.NORMAL, AutoGraderDataProvider.MeasureString.MEASURE_CELL);
  }

  private static void applyBasicStylings(ConfigRegistry config) {
    config.registerConfigAttribute(CellConfigAttributes.CELL_PAINTER, new PaddingDecorator(new TextPainter(), 1));

    Style cellStyle = new Style();
    cellStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.BG_COLOUR);
    cellStyle.setAttributeValue(CellStyleAttributes.FOREGROUND_COLOR, Colours.FG_COLOUR);
    cellStyle.setAttributeValue(CellStyleAttributes.FONT, font);
    cellStyle.setAttributeValue(CellStyleAttributes.HORIZONTAL_ALIGNMENT, hAlign);
    cellStyle.setAttributeValue(CellStyleAttributes.VERTICAL_ALIGNMENT, vAlign);
    cellStyle.setAttributeValue(CellStyleAttributes.BORDER_STYLE, borderStyle);

    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, cellStyle);
    config.registerConfigAttribute(CellConfigAttributes.DISPLAY_CONVERTER, new DefaultDisplayConverter());
  }

  private static void applyGradeStylings(IConfigRegistry config) {
    //A+,..,B get ok stylings.
    Style okGradeStyle = new Style();
    okGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.GRADE_OK);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B);

    //B-,..,C- get warning stylings.
    Style warningGradeStyle = new Style();
    warningGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.GRADE_WARNING);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C_MINUS);

    //D+,..,F-,G,NG all get error stylings. 
    Style errorGradeStyle = new Style();
    errorGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.GRADE_ERROR);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.D_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.D);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.D_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.E_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.E);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.E_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.F_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.F);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.F_MINUS);    
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.G);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, errorGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.NG);

  }

  private static void applyBlankStylings(IConfigRegistry config) {
    Style blankStyle = new Style();
    blankStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, Colours.EMPTY_COLOR);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, blankStyle, DisplayMode.NORMAL, AutoGraderDataProvider.BlankCellData.BLANK_CELL);
  }

  public static class Colours {
    private static final Display display = Display.getDefault();
    public static final Color WHITE = display.getSystemColor(SWT.COLOR_WHITE);
    public static final Color BLACK = display.getSystemColor(SWT.COLOR_BLACK);
    public static final Color GREEN = display.getSystemColor(SWT.COLOR_GREEN);
    public static final Color RED = display.getSystemColor(SWT.COLOR_RED);
    public static final Color PALE_YELLOW = new Color(display, new RGB(255, 255, 204));
    public static final Color PALE_LAVENDER = new Color(display, new RGB(255,240,245)); 
    public static final Color BRIGHT_ORANGE = new Color(display, new RGB(255,165,0));
    public static final Color BRIGHT_GREEN = new Color(display, new RGB(124,252,0));

    public static final Color BG_COLOUR = WHITE;
    public static final Color FG_COLOUR = BLACK;
    public static final Color ENTRY_TITLE_COLOR = PALE_YELLOW;
    public static final Color EMPTY_COLOR = WHITE;
    public static final Color MEASURE_COLOR = PALE_LAVENDER;
    public static final Color GRADE_ERROR = RED;
    public static final Color GRADE_WARNING = BRIGHT_ORANGE;
    public static final Color GRADE_OK = BRIGHT_GREEN;
  }
  
  public static class Fonts {
    private static final Display display = Display.getDefault();
    
    public static final Font DEFAULT_FONT = display.getSystemFont();
    public static final Font BOLD_FONT = makeBold(DEFAULT_FONT);
    
    private static Font makeBold(Font font) {
      FontData[] data = font.getFontData();
      for (FontData fData : data) {
        fData.setStyle(SWT.BOLD);
      }
      return new Font(display, data);
    }
  }
  
}
