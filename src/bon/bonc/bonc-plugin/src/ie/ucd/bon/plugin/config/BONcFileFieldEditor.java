package ie.ucd.bon.plugin.config;

import java.io.File;

import org.eclipse.core.resources.IProject;
import org.eclipse.jface.preference.FileFieldEditor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Layout;

public class BONcFileFieldEditor extends FileFieldEditor {

  private IProject project;
  
  public BONcFileFieldEditor() {
    super();
  }

  public BONcFileFieldEditor(String name, String labelText, boolean enforceAbsolute, Composite parent) {
    super(name, labelText, enforceAbsolute, parent);
  }

  public BONcFileFieldEditor(String name, String labelText, boolean enforceAbsolute, int validationStrategy, Composite parent) {
    super(name, labelText, enforceAbsolute, validationStrategy, parent);
  }

  public BONcFileFieldEditor(String name, String labelText, Composite parent) {
    super(name, labelText, parent);
  }

  /**
   * Helper to open the file chooser dialog.
   * @param startingDirectory the directory to open the dialog on.
   * @return File The File the user selected or <code>null</code> if they
   * do not.
   */
  private File getFile(File startingDirectory) {

    FileDialog dialog = new FileDialog(getShell(), SWT.SAVE | SWT.SHEET);
    if (startingDirectory != null) {
      dialog.setFileName(startingDirectory.getPath());
    } else if (project != null) {
      dialog.setFileName(project.getLocation().toOSString());
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

  @Override
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

  @Override
  protected void createControl(Composite parent) {
    //Override so as not to mess up the GridLayout!
    Layout layout = parent.getLayout();
    if (layout instanceof GridLayout) {
      doFillIntoGrid(parent, getNumberOfControls());
    }
  }  

  public void setProject(IProject project) {
    this.project = project;
  }
  
}
