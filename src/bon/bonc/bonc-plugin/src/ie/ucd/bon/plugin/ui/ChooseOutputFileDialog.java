package ie.ucd.bon.plugin.ui;

import java.io.File;

import net.miginfocom.swt.MigLayout;

import org.eclipse.jface.dialogs.Dialog;
import org.eclipse.jface.window.IShellProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;

public class ChooseOutputFileDialog extends Dialog {

  private File selectedFile;
  
  public ChooseOutputFileDialog(IShellProvider parentShell) {
    super(parentShell);
  }

  public ChooseOutputFileDialog(Shell parentShell) {
    super(parentShell);
  }

  @Override
  protected Control createDialogArea(Composite parent) {
    Composite superControl = (Composite)super.createDialogArea(parent);
    Composite comp = new Composite(superControl, SWT.NONE);
    comp.setLayout(new MigLayout());
    
//    new File
    
    return superControl;
  }

  @Override
  protected void okPressed() {
    // TODO Auto-generated method stub
    super.okPressed();
    
    selectedFile = new File(".");
  }

  public File getSelectedFile() {
    return selectedFile;
  }
    
}
