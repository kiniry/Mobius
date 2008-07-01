package mobius.directVCGen.ui.poview.tree;

import java.io.File;

import mobius.directVCGen.ui.poview.Utils;
import mobius.prover.gui.popup.CompileFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;


public class Goal extends ProofElement implements IShowable {

  private IFile file;
  private File name;
  private File nameVo;
  private String caption;

  public Goal(final IFile file) {
    super(file);
    this.file = file;
    final String tmp = file.getRawLocation().toString();
    name = new File (tmp);
    nameVo = new File(tmp + "o");
    caption = "Goal " + file.getName().substring("goal".length(), file.getName().length() - 2);
  }
  
  public void show() {
    try {
      IDE.openEditor(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage(), file);
    } 
    catch (PartInitException e) {
      e.printStackTrace();
    }
  }
  public String getName() {
    return caption;
  }
  public Image getImage () {
    if (nameVo.exists() && (nameVo.lastModified() > name.lastModified())) {
      return Utils.getImage(IMG_GOAL_SOLVED);
    }
    else {
      return Utils.getImage(IMG_GOAL);
    }
  }

  public void compile(final TreeViewer viewer) {
    if (nameVo.exists() && (nameVo.lastModified() > name.lastModified())) {
      return;
    }
    final Job job = CompileFile.compile(file, true);
    if (job != null) {
      try {
        job.schedule();
        job.join();
      } 
      catch (InterruptedException e) {
        e.printStackTrace();
      }
    }
    Utils.refreshTree(viewer, this);
  }

  public WorkspaceElement createChildFromResource(final IResource res) {
    return null;
  }

  public void update() {
  }
  


}
