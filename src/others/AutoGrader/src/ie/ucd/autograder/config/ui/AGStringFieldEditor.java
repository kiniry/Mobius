package ie.ucd.autograder.config.ui;

import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;

public class AGStringFieldEditor extends StringFieldEditor {

  public AGStringFieldEditor() {
    super();
  }

  public AGStringFieldEditor(String name, String labelText, Composite parent) {
    super(name, labelText, parent);
  }

  public AGStringFieldEditor(String name, String labelText, int width,
      Composite parent) {
    super(name, labelText, width, parent);
  }

  public AGStringFieldEditor(String name, String labelText, int width,
      int strategy, Composite parent) {
    super(name, labelText, width, strategy, parent);
  }

  @Override
  protected void createControl(Composite parent) {
    //Override so as not to mess up the GridLayout!
    Layout layout = parent.getLayout();
    if (layout instanceof GridLayout) {
      doFillIntoGrid(parent, getNumberOfControls());
    }
  }
  
}
