package mobius.prover.gui.preference;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;

public class FileComboFieldEditor extends FieldEditor {
  
  public FileComboFieldEditor(Composite parent, String pref,
                              String comboDesc, String filefieldDesc,
                              String [] [] values) {
    super("", pref, parent);
    createControl(parent);
    ComboFieldEditor fToplevField = new ComboFieldEditor(
            pref, comboDesc,
            values,
            parent);
  
     FileFieldEditor f = new FileFieldEditor(pref,
                                         filefieldDesc,
                                         parent);
     fToplevField.setFileFieldEditor(f);
   f.setEnabled(false, parent);
  }

  public static class ComboFieldEditor extends FieldEditor {

    /**
     * The <code>Combo</code> widget.
     */
    private Combo fCombo;
    
    /**
     * The value (not the name) of the currently selected item in the Combo widget.
     */
    private String fValue;
    
    /**
     * The names (labels) and underlying values to populate the combo widget.  These should be
     * arranged as: { {name1, value1}, {name2, value2}, ...}
     */
    private String[][] fEntryNamesAndValues;

    private FileFieldEditor fFid;

    /**
     * Create the combo box field editor.
     * 
       * @param name the name of the preference this field editor works on
       * @param labelText the label text of the field editor
     * @param entryNamesAndValues the names (labels) and underlying values to populate the combo widget.  These should be
     * arranged as: { {name1, value1}, {name2, value2}, ...}
     * @param parent the parent composite
     */
    public ComboFieldEditor(String name, String labelText, String[][] entryNamesAndValues,
                            Composite parent) {
      init(name, labelText);
      fEntryNamesAndValues = entryNamesAndValues;
      createControl(parent);    
    }



    public void setFileFieldEditor(FileFieldEditor f) {
      fFid = f;
    }



    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#adjustForNumColumns(int)
     */
    protected void adjustForNumColumns(int numColumns) {
      if (numColumns > 1) {
        Control control = getLabelControl();
        int left = numColumns;
        if (control != null) {
          ((GridData)control.getLayoutData()).horizontalSpan = 1;
          left = left - 1;
        }
        ((GridData)fCombo.getLayoutData()).horizontalSpan = left;
      } else {
        Control control = getLabelControl();
        if (control != null) {
          ((GridData)control.getLayoutData()).horizontalSpan = 1;
        }
        ((GridData)fCombo.getLayoutData()).horizontalSpan = 1;      
      }
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#doFillIntoGrid(org.eclipse.swt.widgets.Composite, int)
     */
    protected void doFillIntoGrid(Composite parent, int numColumns) {
      int comboC = 1;
      if (numColumns > 1) {
        comboC = numColumns - 1;
      }
      Control control = getLabelControl(parent);
      GridData gd = new GridData();
      gd.horizontalSpan = 1;
      control.setLayoutData(gd);
      control = getComboBoxControl(parent);
      gd = new GridData();
      gd.horizontalSpan = comboC;
      gd.horizontalAlignment = GridData.FILL;
      control.setLayoutData(gd);
      control.setFont(parent.getFont());
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#doLoad()
     */
    protected void doLoad() {
      updateComboForValue(getPreferenceStore().getString(getPreferenceName()));
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#doLoadDefault()
     */
    protected void doLoadDefault() {
      updateComboForValue(getPreferenceStore().getDefaultString(getPreferenceName()));
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#doStore()
     */
    protected void doStore() {
      if (fValue == null) {
        getPreferenceStore().setToDefault(getPreferenceName());
        return;
      }
      getPreferenceStore().setValue(getPreferenceName(), fValue);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.preference.FieldEditor#getNumberOfControls()
     */
    public int getNumberOfControls() {
      return 2;
    }

    /*
     * Lazily create and return the Combo control.
     */
    private Combo getComboBoxControl(final Composite parent) {
      if (fCombo == null) {
        fCombo = new Combo(parent, SWT.READ_ONLY);
        fCombo.setFont(parent.getFont());
        for (int i = 0; i < fEntryNamesAndValues.length; i++) {
          fCombo.add(fEntryNamesAndValues[i][0], i);
        }
        fCombo.add("Custom...");
        
        fCombo.addSelectionListener(new SelectionAdapter() {
          public void widgetSelected(SelectionEvent evt) {
            String oldValue = fValue;
            String name = fCombo.getText();
            if (name.equals("Custom...")) {
              fValue = "Custom";
              fFid.setEnabled(true, parent);
            }
            else {
              
              fValue = getValueForName(name);
              fFid.setEnabled(false, parent); 
            }

            setPresentsDefaultValue(false);
            fireValueChanged(VALUE, oldValue, fValue);          
          }
        });
      }
      return fCombo;
    }
    
    /*
     * Given the name (label) of an entry, return the corresponding value.
     */
    private String getValueForName(String name) {
      for (int i = 0; i < fEntryNamesAndValues.length; i++) {
        String[] entry = fEntryNamesAndValues[i];
        if (name.equals(entry[0])) {
          return entry[1];
        }
      }
      return fEntryNamesAndValues[0][0];
    }
    
    /*
     * Set the name in the combo widget to match the specified value.
     */
    private void updateComboForValue(String value) {
      fValue = value;
      for (int i = 0; i < fEntryNamesAndValues.length; i++) {
        if (value.equals(fEntryNamesAndValues[i][1])) {
          fCombo.setText(fEntryNamesAndValues[i][0]);
          return;
        }
      }
      if (fEntryNamesAndValues.length > 0) {
        fValue = fEntryNamesAndValues[0][1];
        fCombo.setText(fEntryNamesAndValues[0][0]);
      }
    }

    /*
     * (non-Javadoc)
     * 
     * @see org.eclipse.jface.preference.FieldEditor#setEnabled(boolean,
     *      org.eclipse.swt.widgets.Composite)
     */
    public void setEnabled(boolean enabled, Composite parent) {
      super.setEnabled(enabled, parent);
      getComboBoxControl(parent).setEnabled(enabled);
    }
  }

  @Override
  protected void adjustForNumColumns(int numColumns) {
    // TODO Auto-generated method stub
    
  }

  @Override
  protected void doFillIntoGrid(Composite parent, int numColumns) {
    // TODO Auto-generated method stub
    
  }

  @Override
  protected void doLoad() {
    // TODO Auto-generated method stub
    
  }

  @Override
  protected void doLoadDefault() {
    // TODO Auto-generated method stub
    
  }

  @Override
  protected void doStore() {
    // TODO Auto-generated method stub
    
  }

  @Override
  public int getNumberOfControls() {
    // TODO Auto-generated method stub
    return 0;
  }
}
