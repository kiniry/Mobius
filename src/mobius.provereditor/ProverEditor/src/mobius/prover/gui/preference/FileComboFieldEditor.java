package mobius.prover.gui.preference;

import java.io.File;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.StringButtonFieldEditor;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.FileDialog;

public class FileComboFieldEditor extends FieldEditor {
  private final ComboFieldEditor fCombo;
  private final FileFieldEditor fFileField;
  final Composite c;
  public FileComboFieldEditor(Composite parent, String pref,
                              String comboDesc, String filefieldDesc,
                              String [] [] values) {
    super("", pref, parent);
    
    c = new Composite(parent, SWT.NONE);
    fCombo = new ComboFieldEditor(
            pref, comboDesc,
            values,
            c);
   // new Composite(c, SWT.NONE);
    fFileField = new FileFieldEditor(pref, filefieldDesc, c);
    fCombo.setFileFieldEditor(fFileField);
    fFileField.setEnabled(false, c);
    createControl(parent);
  }
  
  @Override
  protected void adjustForNumColumns(final int numCol) {
    fCombo.adjustForNumColumns(numCol);
  }

  @Override
  protected void doFillIntoGrid(Composite parent, int numColumns) {
    Assert.isTrue(numColumns >= getNumberOfControls());
    Assert.isTrue(parent.getLayout() instanceof GridLayout);
    if (fCombo == null) {
      return;
    }
    fCombo.fillIntoGrid(c, numColumns);
    fFileField.fillIntoGrid(c, numColumns);
    
  }


  @Override
  protected void doLoad() {
    fCombo.doLoad();
  }

  @Override
  protected void doLoadDefault() {
    fCombo.doLoadDefault();
  }

  @Override
  protected void doStore() {
    fCombo.doStore();
  }

  @Override
  public int getNumberOfControls() {
    return 3;
  }
  
  public void setPreferenceStore(IPreferenceStore store) {
    super.setPreferenceStore(store);
    fCombo.setPreferenceStore(store);
    fFileField.setPreferenceStore(store);
  }
  
  public static class ComboFieldEditor extends FieldEditor {

    public final static String[] customEntry = {"Custom...", "Custom"}; 
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
    private Composite parent;

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
      this.parent = parent;
      createControl(parent);    
      
    }



    public void setFileFieldEditor(FileFieldEditor f) {
      fFid = f;
    }

    /** {@inheritDoc} */
    protected void adjustForNumColumns(final int numColumns) {
      if (numColumns > 1) {
        final Control control = getLabelControl();
        int left = numColumns;
        if (control != null) {
          ((GridData)control.getLayoutData()).horizontalSpan = 1;
          left = left - 1;
        }
        ((GridData)fCombo.getLayoutData()).horizontalSpan = left;
      } 
      else {
        final Control control = getLabelControl();
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
      if (fValue.equals(customEntry[1])) {
       fFid.doStore();
      }
      else {
        getPreferenceStore().setValue(getPreferenceName(), fValue);
      }
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
        fCombo.add(customEntry[0]);
        
        fCombo.addSelectionListener(new SelectionAdapter() {
          public void widgetSelected(SelectionEvent evt) {
            final String oldValue = fValue;
            final String name = fCombo.getText();
            if (name.equals(customEntry[0])) {
              fValue = customEntry[1];
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
      return customEntry[0];
    }
    
    /*
     * Set the name in the combo widget to match the specified value.
     */
    private void updateComboForValue(String value) {
      fValue = value;
      for (int i = 0; i < fEntryNamesAndValues.length; i++) {
        if (value.equals(fEntryNamesAndValues[i][1])) {
          fCombo.setText(fEntryNamesAndValues[i][0]);
          fFid.setEnabled(false, parent);
          return;
        }
      }
      
      if (fEntryNamesAndValues.length > 0) {
        fValue = customEntry[1];
        fCombo.setText(customEntry[0]);
        fFid.setEnabled(true, parent);
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
  public static class FileFieldEditor extends StringButtonFieldEditor {

    /**
     * List of legal file extension suffixes, or <code>null</code>
     * for system defaults.
     */
    private String[] extensions = null;

    /**
     * Indicates whether the path must be absolute;
     * <code>false</code> by default.
     */
    private boolean enforceAbsolute = false;

    /**
     * Creates a new file field editor 
     */
    protected FileFieldEditor() {
    }

    /**
     * Creates a file field editor.
     * 
     * @param name the name of the preference this field editor works on
     * @param labelText the label text of the field editor
     * @param parent the parent of the field editor's control
     */
    public FileFieldEditor(String name, String labelText, Composite parent) {
        this(name, labelText, false, parent);
    }
    
    /**
     * Creates a file field editor.
     * 
     * @param name the name of the preference this field editor works on
     * @param labelText the label text of the field editor
     * @param enforceAbsolute <code>true</code> if the file path
     *  must be absolute, and <code>false</code> otherwise
     * @param parent the parent of the field editor's control
     */
    public FileFieldEditor(String name, String labelText, boolean enforceAbsolute, Composite parent) {
        this(name, labelText, enforceAbsolute, VALIDATE_ON_FOCUS_LOST, parent);
    }
    /**
     * Creates a file field editor.
     * 
     * @param name the name of the preference this field editor works on
     * @param labelText the label text of the field editor
     * @param enforceAbsolute <code>true</code> if the file path
     *  must be absolute, and <code>false</code> otherwise
     * @param validationStrategy either {@link StringButtonFieldEditor#VALIDATE_ON_KEY_STROKE}
     *  to perform on the fly checking, or {@link StringButtonFieldEditor#VALIDATE_ON_FOCUS_LOST}
     *  (the default) to perform validation only after the text has been typed in
     * @param parent the parent of the field editor's control.
     * @since 3.4
     * @see StringButtonFieldEditor#VALIDATE_ON_KEY_STROKE
     * @see StringButtonFieldEditor#VALIDATE_ON_FOCUS_LOST
     */
    public FileFieldEditor(String name, String labelText,
            boolean enforceAbsolute, int validationStrategy, Composite parent) {
        init(name, labelText);
        this.enforceAbsolute = enforceAbsolute;
        setErrorMessage(JFaceResources
                .getString("FileFieldEditor.errorMessage"));//$NON-NLS-1$
        setChangeButtonText(JFaceResources.getString("openBrowse"));//$NON-NLS-1$
        setValidateStrategy(validationStrategy);
        createControl(parent);
    }

    /* (non-Javadoc)
     * Method declared on StringButtonFieldEditor.
     * Opens the file chooser dialog and returns the selected file.
     */
    protected String changePressed() {
        File f = new File(getTextControl().getText());
        if (!f.exists()) {
      f = null;
    }
        File d = getFile(f);
        if (d == null) {
      return null;
    }

        return d.getAbsolutePath();
    }

    /* (non-Javadoc)
     * Method declared on StringFieldEditor.
     * Checks whether the text input field specifies an existing file.
     */
    protected boolean checkState() {

        String msg = null;

        String path = getTextControl().getText();
        if (path != null) {
      path = path.trim();
    } else {
      path = "";//$NON-NLS-1$
    }
        if (path.length() == 0) {
            if (!isEmptyStringAllowed()) {
        msg = getErrorMessage();
      }
        } else {
            File file = new File(path);
            if (file.isFile()) {
                if (enforceAbsolute && !file.isAbsolute()) {
          msg = JFaceResources
                            .getString("FileFieldEditor.errorMessage2");//$NON-NLS-1$
        }
            } else {
                msg = getErrorMessage();
            }
        }

        if (msg != null) { // error
            showErrorMessage(msg);
            return false;
        }

        // OK!
        clearErrorMessage();
        return true;
    }

    /**
     * Helper to open the file chooser dialog.
     * @param startingDirectory the directory to open the dialog on.
     * @return File The File the user selected or <code>null</code> if they
     * do not.
     */
    private File getFile(File startingDirectory) {

        FileDialog dialog = new FileDialog(getShell(), SWT.OPEN | SWT.SHEET);
        if (startingDirectory != null) {
      dialog.setFileName(startingDirectory.getPath());
    }
        if (extensions != null) {
      dialog.setFilterExtensions(extensions);
    }
        String file = dialog.open();
        if (file != null) {
            file = file.trim();
            if (file.length() > 0) {
        return new File(file);
      }
        }

        return null;
    }
    public void doStore() {
      super.doStore();
    }
    /**
     * Sets this file field editor's file extension filter.
     *
     * @param extensions a list of file extension, or <code>null</code> 
     * to set the filter to the system's default value
     */
    public void setFileExtensions(String[] extensions) {
        this.extensions = extensions;
    }
}


}
