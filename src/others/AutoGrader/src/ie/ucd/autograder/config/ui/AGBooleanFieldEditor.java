package ie.ucd.autograder.config.ui;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;

public class AGBooleanFieldEditor extends BooleanFieldEditor {

  public AGBooleanFieldEditor() {
  }

  public AGBooleanFieldEditor(String name, String label, Composite parent) {
    super(name, label, parent);
  }

  public AGBooleanFieldEditor(String name, String labelText, int style,
      Composite parent) {
    super(name, labelText, style, parent);
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
