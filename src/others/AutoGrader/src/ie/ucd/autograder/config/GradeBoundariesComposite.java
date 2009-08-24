package ie.ucd.autograder.config;

import ie.ucd.autograder.grading.Grade;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FormLayout;
import org.eclipse.swt.widgets.Composite;

public class GradeBoundariesComposite extends Composite {

  final List<FieldEditor> fieldEditors;
  
  public GradeBoundariesComposite(Composite parent) {
    super(parent, SWT.NULL);
    
    this.setLayout(new FormLayout());
    
    fieldEditors = new ArrayList<FieldEditor>();
  }

  private void createFormItems() {
    
    for (Grade grade : Grade.values()) {
      BooleanFieldEditor enabled = new BooleanFieldEditor("xxx", "enabled", this);
      FloatFieldEditor gradeValue = new FloatFieldEditor("xxx", "value", this);
      gradeValue.setValidRange(0, 100);
    }
    
  }
  
  
  public boolean performOk() {
    
    return true;
  }
  
}
