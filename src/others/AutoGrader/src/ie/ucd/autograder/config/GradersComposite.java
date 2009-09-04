package ie.ucd.autograder.config;

import ie.ucd.autograder.AutoGraderPlugin;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferencePage;
import org.eclipse.jface.preference.StringFieldEditor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Label;

public class GradersComposite extends Composite {

  private final static int GRID_WIDTH = 8;
  private final static String METRICS_ID = "metrics";
  
  private final List<Grader> graders;
  
  public GradersComposite(Composite parent, PreferencePage prefPage) {
    super(parent, SWT.NONE);
   
    this.setLayout(new FillLayout());
    
    this.graders = new ArrayList<Grader>();
    
    createFormItems(prefPage);
  }
  
  private void createFormItems(PreferencePage prefPage) {
    
    IPreferenceStore prefStore = prefPage.getPreferenceStore();
    String gradersList = prefStore.getString(AutoGraderPlugin.PLUGIN_ID + ".collectors");
        
    //TODO add metrics config
    
    ExpandBar expandBar = new ExpandBar(this, SWT.V_SCROLL);
    
    //Should not be null/empty due to defaults
    String[] gradersArr = gradersList.split(",");
    for (String graderName : gradersArr) {
      graderName = graderName.trim();
      if (!graderName.equals("") && !graderName.equals(METRICS_ID)) {
        Grader grader = new Grader(expandBar, prefPage, graderName);
        graders.add(grader);
        ExpandItem expandItem = new ExpandItem(expandBar, SWT.NONE);
        expandItem.setHeight(grader.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
        expandItem.setControl(grader);
        expandItem.setExpanded(false);
        grader.setExpandItem(expandItem);
      }
    }    
  }
  
  public boolean performOk() {
    for (Grader g : graders) {
      if (!g.performOk()) {
        return false;
      }
    }

    //TODO store graders ids
    
    return true;
  }
  
  
  public void setPreferenceStore(IPreferenceStore store) {
    for (Grader grader : graders) {
      grader.setPreferenceStore(store);
    }
  }
  
  private class Grader extends Composite implements IPropertyChangeListener {
    private ExpandItem expandItem;
    private final StringFieldEditor displayName;
    private final BooleanFieldEditor enabled;
    private final FloatFieldEditor graderWeight;
    private final StringFieldEditor markerIds;
    private final BooleanFieldEditor divLoc;
    private final BooleanFieldEditor errorsEnabled;
    private final BooleanFieldEditor warningsEnabled;
    private final StringFieldEditor errorsLookup;
    private final StringFieldEditor warningsLookup;
    private final FloatFieldEditor errorsWeight;
    private final FloatFieldEditor warningsWeight;
    private final List<FieldEditor> fieldEditors;
    
    public Grader(Composite parent, PreferencePage prefPage, String graderId) {
      super(parent, SWT.NONE);
      GridLayout layout = new GridLayout();
      layout.marginWidth = 3;
      layout.marginHeight = 3;
      layout.numColumns = GRID_WIDTH;
      this.setLayout(layout);
      
      String id = AutoGraderPlugin.PLUGIN_ID + ".collectors." + graderId + '.';
      //TODO label
      fieldEditors = new ArrayList<FieldEditor>(12);
      
      int rowItems = 0;
      enabled = new AGBooleanFieldEditor(id + "enabled", "Enabled?", this);
      enabled.setPropertyChangeListener(this);
      rowItems += enabled.getNumberOfControls();
      displayName = new AGStringFieldEditor(id + "displayname", "Display name", this);
      rowItems += displayName.getNumberOfControls();
      graderWeight = new FloatFieldEditor(id + "overallweight", "Grader weight", this);
      graderWeight.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      rowItems = 0;
      markerIds = new AGStringFieldEditor(id + "markerids", "Marker ids", this);
      markerIds.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      rowItems = 0;
      divLoc = new AGBooleanFieldEditor(id + "divkloc", "Scale by kloc?", this);
      divLoc.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      rowItems = 0;
      errorsEnabled = new AGBooleanFieldEditor(id + "errorsenabled", "Errors enabled?", this);
      errorsEnabled.setPropertyChangeListener(this);
      rowItems += errorsEnabled.getNumberOfControls();
      errorsWeight = new FloatFieldEditor(id + "errorsweight", "Errors weight", this);
      rowItems += errorsWeight.getNumberOfControls();
      errorsLookup = new AGStringFieldEditor(id + "errorslookup", "Errors lookup", this);
      errorsLookup.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      rowItems = 0;
      warningsEnabled = new AGBooleanFieldEditor(id + "warningsenabled", "Warnings enabled?", this);
      warningsEnabled.setPropertyChangeListener(this);
      rowItems += warningsEnabled.getNumberOfControls();
      warningsWeight = new FloatFieldEditor(id + "warningsweight", "Warnings weight", this);
      rowItems += warningsWeight.getNumberOfControls();
      warningsLookup = new AGStringFieldEditor(id + "warningslookup", "Warnings lookup", this);
      warningsLookup.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      Label sep = new Label(this, SWT.SEPARATOR | SWT.HORIZONTAL);
      GridData sepData = new GridData();
      sepData.horizontalAlignment  = SWT.FILL;
      sepData.horizontalSpan = GRID_WIDTH;
      sepData.grabExcessHorizontalSpace = true;
      sep.setLayoutData(sepData);
      
      addFieldEditors(enabled, displayName, graderWeight, markerIds, divLoc, errorsEnabled, errorsWeight, errorsLookup, warningsEnabled, warningsWeight, warningsLookup);
      setPreferencePage(prefPage);
    }
    
    private void addFieldEditor(FieldEditor fe) {
      fieldEditors.add(fe);
    }
    
    private void addFieldEditors(FieldEditor... fes) {
      for (FieldEditor fe : fes) {
        addFieldEditor(fe);
      }
    }
    
    public void setPreferenceStore(IPreferenceStore store) {
      for (FieldEditor fe : fieldEditors) {
        fe.setPreferenceStore(store);
        fe.load();
      }
      if (expandItem != null) {
        expandItem.setText(displayName.getStringValue());
      }
      updateEnabledness();
    }
    
    public void setPreferencePage(PreferencePage prefPage) {
      for (FieldEditor fe : fieldEditors) {
        fe.setPage(prefPage);
      }
    }

    public void propertyChange(PropertyChangeEvent event) {
      updateEnabledness();      
    }
    
    private void updateEnabledness() {
      boolean allEnabled = enabled.getBooleanValue();
      boolean errEnabled = errorsEnabled.getBooleanValue();
      boolean warnEnabled = warningsEnabled.getBooleanValue();
      
      displayName.setEnabled(allEnabled, this);
      graderWeight.setEnabled(allEnabled, this);
      markerIds.setEnabled(allEnabled, this);
      divLoc.setEnabled(allEnabled, this);
      errorsEnabled.setEnabled(allEnabled, this);
      warningsEnabled.setEnabled(allEnabled, this);
      
      errorsWeight.setEnabled(allEnabled && errEnabled, this);
      errorsLookup.setEnabled(allEnabled && errEnabled, this);
      
      warningsWeight.setEnabled(allEnabled && warnEnabled, this);
      warningsLookup.setEnabled(allEnabled && warnEnabled, this);
    }
    
    public boolean performOk() {
      for (FieldEditor editor : fieldEditors) {
        if (!editor.isValid()) {
          return false;
        }
        editor.store();
      }
      if (expandItem != null) {
        expandItem.setText(displayName.getStringValue());
      }
      return true;
    }

    public void setExpandItem(ExpandItem expandItem) {
      this.expandItem = expandItem;
      expandItem.setText(displayName.getStringValue());
    }   
    
    
  }
  
}
