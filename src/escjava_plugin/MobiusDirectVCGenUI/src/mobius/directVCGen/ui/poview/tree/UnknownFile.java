package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;


public class UnknownFile extends AWorkspaceElement implements IShowable {

  final IFile file;
  UnknownFile(final IFile key) {
    super(key);
    file = key;
    
  }

  public AWorkspaceElement createChildFromResource(final IResource res) {
    return null;
  }

  public void update() {
  }

  public String getName() {
    return file.getName();
  }
  public Image getImage () {
    return Utils.getImage(IMG_UNKNOWN);
  }
  
  public void show() {
    try {
      final IWorkbench bench = PlatformUI.getWorkbench();
      final IWorkbenchPage page = bench.getActiveWorkbenchWindow().getActivePage(); 
      IDE.openEditor(page, file);
    } 
    catch (PartInitException e) {
      e.printStackTrace();
    }
  }
}
