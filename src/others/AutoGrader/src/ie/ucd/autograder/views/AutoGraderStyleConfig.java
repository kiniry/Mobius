package ie.ucd.autograder.views;

import ie.ucd.autograder.grading.Grade;
import net.sourceforge.nattable.config.AbstractRegistryConfiguration;
import net.sourceforge.nattable.config.CellConfigAttributes;
import net.sourceforge.nattable.config.ConfigRegistry;
import net.sourceforge.nattable.config.IConfigRegistry;
import net.sourceforge.nattable.style.CellStyleAttributes;
import net.sourceforge.nattable.style.DisplayMode;
import net.sourceforge.nattable.style.Style;

public class AutoGraderStyleConfig extends AbstractRegistryConfiguration {
    
  public void configureRegistry(ConfigRegistry configRegistry) {
    applyGradeStylings(configRegistry);
  }

  private static void applyGradeStylings(IConfigRegistry config) {
    //A+,..,B get ok stylings.
    Style okGradeStyle = new Style();
    okGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, AutoGraderView.GRADE_OK);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.A_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, okGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B);

    //B-,..,C- get warning stylings.
    Style warningGradeStyle = new Style();
    warningGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, AutoGraderView.GRADE_WARNING);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.B_MINUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C_PLUS);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C);
    config.registerConfigAttribute(CellConfigAttributes.CELL_STYLE, warningGradeStyle, DisplayMode.NORMAL, AutoGraderDataProvider.GradeHolder.GRADE + Grade.C_MINUS);

    //D+,..,F-,G,NG all get error stylings. 
    Style errorGradeStyle = new Style();
    errorGradeStyle.setAttributeValue(CellStyleAttributes.BACKGROUND_COLOR, AutoGraderView.GRADE_ERROR);
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
  
}
