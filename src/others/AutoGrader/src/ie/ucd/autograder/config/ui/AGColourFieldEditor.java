package ie.ucd.autograder.config.ui;

import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;

public class AGColourFieldEditor extends ColorFieldEditor {

  public AGColourFieldEditor() {
    super();
  }

  public AGColourFieldEditor(String name, String labelText, Composite parent) {
    super(name, labelText, parent);
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
