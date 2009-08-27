package ie.ucd.autograder.config;

import ie.ucd.autograder.grading.Grade;
import ie.ucd.autograder.util.Pair;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.ColorFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;

public class GradeBoundariesComposite extends Composite {

  private final List<FieldEditor> fieldEditors;
  private final List<Pair<BooleanFieldEditor,List<FieldEditor>>> fieldEditorPairs;
  private final static int GRID_WIDTH = 8;
  
  
  public GradeBoundariesComposite(Composite parent, PreferencePage prefPage) {
    super(parent, SWT.NULL);
    fieldEditors = new ArrayList<FieldEditor>();
    fieldEditorPairs = new ArrayList<Pair<BooleanFieldEditor,List<FieldEditor>>>();
    
    GridLayout layout = new GridLayout();
    layout.marginWidth = 3;
    layout.marginHeight = 3;
    layout.numColumns = GRID_WIDTH;
    
    this.setLayout(layout);
    createFormItems(prefPage);
  }

  private void createFormItems(PreferencePage prefPage) {
    for (Grade grade : Grade.values()) {
      Label label = new Label(this, SWT.NONE);
      label.setText("Grade " + grade.toString());
      GridData labelData = new GridData();
      labelData.horizontalAlignment = SWT.LEFT;
      label.setLayoutData(labelData);
      
      final BooleanFieldEditor enabled = new AGBooleanFieldEditor("gradeboundaries."+grade.name()+".enabled", "enabled?", this);
      enabled.setPage(prefPage);
      fieldEditors.add(enabled);
      final FloatFieldEditor gradeValue = new FloatFieldEditor("gradeboundaries."+grade.name()+".value", "value", this);
      gradeValue.setPage(prefPage);
      fieldEditors.add(gradeValue);
      gradeValue.setValidRange(0, 100);
      ColorFieldEditor colourChooser = new AGColourFieldEditor("gradeboundaries." + grade.name() + ".colour", "colour", this);
      colourChooser.setPage(prefPage);
      fieldEditors.add(colourChooser);
      
      List<FieldEditor> enableList = new ArrayList<FieldEditor>(2);
      enableList.add(gradeValue);
      enableList.add(colourChooser);
      fieldEditorPairs.add(new Pair<BooleanFieldEditor,List<FieldEditor>>(enabled, enableList));
      
      gradeValue.setEnabled(enabled.getBooleanValue(), this);
      enabled.setPropertyChangeListener(new IPropertyChangeListener() {
        public void propertyChange(PropertyChangeEvent event) {
          updateEnabledness();
        }
      });
      
      Label sep = new Label(this, SWT.SEPARATOR | SWT.HORIZONTAL);
      GridData sepData = new GridData();
      sepData.horizontalAlignment  = SWT.FILL;
      sepData.horizontalSpan = GRID_WIDTH;
      sepData.grabExcessHorizontalSpace = true;
      sep.setLayoutData(sepData);
    }
    
  }
  
  public boolean performOk(IPreferenceStore store) {
    for (FieldEditor fe : fieldEditors) {
      if (!fe.isValid()) {
        return false;
      }
    }
    
    for (FieldEditor fe : fieldEditors) {
      fe.store();
    }
    
    return true;
  }
  
  public void setPreferenceStore(IPreferenceStore store) {
    for (FieldEditor fe : fieldEditors) {
      fe.setPreferenceStore(store);
      fe.load();
    }
    updateEnabledness();
  }
  
  public void updateEnabledness() {
    for (Pair<BooleanFieldEditor,List<FieldEditor>> pair : fieldEditorPairs) {
      boolean enabled = pair.getFirst().getBooleanValue();
      for (FieldEditor editor : pair.getSecond()) {
        editor.setEnabled(enabled, this);
      }
    }
  }
  
}
