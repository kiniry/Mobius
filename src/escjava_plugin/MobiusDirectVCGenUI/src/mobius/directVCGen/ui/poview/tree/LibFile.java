package mobius.directVCGen.ui.poview.tree;

import java.io.File;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;


public class LibFile extends AWorkspaceElement implements IShowable {
  private final IFile file;
  private final File fileVo;
  
  LibFile(final IFile key) {
    super(key);
    file = key;
    final String tmp = file.getRawLocation().toString();
    fileVo = new File(tmp + "o");
    
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
    if (fileVo.exists()) {
      return Utils.getImage(IMG_LIB_RED);
    }
    else {
      return Utils.getImage(IMG_LIB);
    }
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
