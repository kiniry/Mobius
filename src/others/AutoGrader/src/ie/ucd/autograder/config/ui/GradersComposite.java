package ie.ucd.autograder.config.ui;

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
   
    ExpandBar expandBar = new ExpandBar(this, SWT.V_SCROLL);
    
    Grader metricsGrader = new MetricsGrader(expandBar, prefPage);
    setupGrader(metricsGrader, expandBar, prefStore);
    
    //Should not be null/empty due to defaults
    String[] gradersArr = gradersList.split(",");
    for (String graderName : gradersArr) {
      graderName = graderName.trim();
      if (!graderName.equals("") && !graderName.equals(METRICS_ID)) {
        Grader grader = new OrdinaryGrader(expandBar, prefPage, graderName);
        setupGrader(grader, expandBar, prefStore);
      }
    }    
  }
  
  private void setupGrader(Grader grader, ExpandBar expandBar, IPreferenceStore store) {
    graders.add(grader);
    ExpandItem expandItem = new ExpandItem(expandBar, SWT.NONE);
    expandItem.setHeight(grader.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
    expandItem.setControl(grader);
    expandItem.setExpanded(false);
    grader.setExpandItem(expandItem);
    grader.setPreferenceStore(store);
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
  
  private abstract class Grader extends Composite implements IPropertyChangeListener {
    private ExpandItem expandItem;
    private final List<FieldEditor> fieldEditors;
    protected final StringFieldEditor displayName;
    protected final BooleanFieldEditor enabled;
    protected final FloatFieldEditor graderWeight;    
    
    public Grader(Composite parent, PreferencePage prefPage, String graderId) {
      super(parent, SWT.NONE);
      GridLayout layout = new GridLayout();
      layout.marginWidth = 3;
      layout.marginHeight = 3;
      layout.numColumns = GRID_WIDTH;
      this.setLayout(layout);
      
      fieldEditors = new ArrayList<FieldEditor>();
      
      String id = AutoGraderPlugin.PLUGIN_ID + ".collectors." + graderId + '.';
      
      int rowItems = 0;
      enabled = new AGBooleanFieldEditor(id + "enabled", "Enabled?", this);
      enabled.setPropertyChangeListener(this);
      rowItems += enabled.getNumberOfControls();
      displayName = new AGStringFieldEditor(id + "displayname", "Display name", this);
      rowItems += displayName.getNumberOfControls();
      graderWeight = new FloatFieldEditor(id + "overallweight", "Grader weight", this);
      graderWeight.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      addFieldEditors(displayName, enabled, graderWeight);
    }
    
    protected void addFieldEditor(FieldEditor fe) {
      fieldEditors.add(fe);
    }
    
    protected void addFieldEditors(FieldEditor... fes) {
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
    
    public void propertyChange(PropertyChangeEvent event) {
      updateEnabledness();      
    }
    
    protected abstract void updateEnabledness();
  }
  
  private class MetricsGrader extends Grader implements IPropertyChangeListener {
    public static final String ID = "metrics"; 
    
    private final BooleanFieldEditor methodLocEnabled;
    private final BooleanFieldEditor methodCcEnabled;
    private final FloatFieldEditor methodLocWeight;
    private final FloatFieldEditor methodCcWeight;
    private final StringFieldEditor methodLocLookup;
    private final StringFieldEditor methodCcLookup;
    
    public MetricsGrader(Composite parent, PreferencePage prefPage) {
      super(parent, prefPage, ID);
      
      String id = AutoGraderPlugin.PLUGIN_ID + ".collectors." + ID + '.';
      
      int rowItems = 0;
      Label label = new Label(this, SWT.NONE);
      label.setText("Average method LOC");
      rowItems ++;
      methodLocEnabled = new AGBooleanFieldEditor(id + "methodloc.enabled", "enabled?", this);
      methodLocEnabled.setPropertyChangeListener(this);
      rowItems += methodLocEnabled.getNumberOfControls();
      methodLocWeight = new FloatFieldEditor(id + "methodloc.weight", "weight", this);
      rowItems += methodLocWeight.getNumberOfControls();
      methodLocLookup = new AGStringFieldEditor(id + "methodloc.lookup", "lookup", this);
      methodLocLookup.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      rowItems = 0;
      label = new Label(this, SWT.NONE);
      label.setText("Average method CC");
      rowItems ++;
      methodCcEnabled = new AGBooleanFieldEditor(id + "methodcc.enabled", "enabled?", this);
      methodCcEnabled.setPropertyChangeListener(this);
      rowItems += methodCcEnabled.getNumberOfControls();
      methodCcWeight = new FloatFieldEditor(id + "methodcc.weight", "weight", this);
      rowItems += methodCcWeight.getNumberOfControls();
      methodCcLookup = new AGStringFieldEditor(id + "methodcc.lookup", "lookup", this);
      methodCcLookup.fillIntoGrid(this, GRID_WIDTH - rowItems);
      
      addFieldEditors(methodLocEnabled, methodLocWeight, methodLocLookup, methodCcEnabled, methodCcWeight, methodCcLookup);
    }

    @Override
    protected void updateEnabledness() {
      boolean allEnabled = enabled.getBooleanValue();
      boolean mlocEnabled = methodLocEnabled.getBooleanValue();
      boolean mccEnabled = methodCcEnabled.getBooleanValue();
      
      displayName.setEnabled(allEnabled, this);
      graderWeight.setEnabled(allEnabled, this);
      
      methodLocEnabled.setEnabled(allEnabled, this);
      methodCcEnabled.setEnabled(allEnabled, this);
      
      methodLocWeight.setEnabled(allEnabled && mlocEnabled, this);
      methodLocLookup.setEnabled(allEnabled && mlocEnabled, this);
      
      methodCcWeight.setEnabled(allEnabled && mccEnabled, this);
      methodCcLookup.setEnabled(allEnabled && mccEnabled, this);
    }
  }
  
  private class OrdinaryGrader extends Grader implements IPropertyChangeListener {
    private final StringFieldEditor markerIds;
    private final BooleanFieldEditor divLoc;
    private final BooleanFieldEditor errorsEnabled;
    private final BooleanFieldEditor warningsEnabled;
    private final StringFieldEditor errorsLookup;
    private final StringFieldEditor warningsLookup;
    private final FloatFieldEditor errorsWeight;
    private final FloatFieldEditor warningsWeight;
    
    
    public OrdinaryGrader(Composite parent, PreferencePage prefPage, String graderId) {
      super(parent, prefPage, graderId);
      
      String id = AutoGraderPlugin.PLUGIN_ID + ".collectors." + graderId + '.';
   
      int rowItems = 0;
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
      
      addFieldEditors(markerIds, divLoc, errorsEnabled, errorsWeight, errorsLookup, warningsEnabled, warningsWeight, warningsLookup);
      setPreferencePage(prefPage);
    }

    protected void updateEnabledness() {
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
    
  }
  
}
