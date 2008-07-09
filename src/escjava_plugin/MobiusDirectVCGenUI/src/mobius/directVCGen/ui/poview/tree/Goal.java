package mobius.directVCGen.ui.poview.tree;

import java.io.File;

import mobius.directVCGen.ui.poview.util.ImagesUtils;
import mobius.directVCGen.ui.poview.util.RefreshUtils;
import mobius.prover.gui.popup.CompileFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;


public class Goal extends UnknownFile implements IShowable {

  private final File fName;
  private final File fNameVo;
  private final String fCaption;

  public Goal(final IFile file) {
    super(file);
    final String tmp = file.getRawLocation().toString();
    fName = new File (tmp);
    fNameVo = new File(tmp + "o");
    fCaption = "Goal " + file.getName().substring("goal".length(), 
                                                  file.getName().length() - 2);
  }
    
  /** {@inheritDoc}  */
  public String getName() {
    return fCaption;
  }
  
  /** {@inheritDoc} */
  public Image getImage () {
    if (fNameVo.exists() && (fNameVo.lastModified() > fName.lastModified())) {
      return ImagesUtils.getImage(IMG_GOAL_SOLVED);
    }
    else {
      return ImagesUtils.getImage(IMG_GOAL);
    }
  }

  /** {@inheritDoc} */
  public void compile(final TreeViewer viewer) {
    if (fNameVo.exists() && (fNameVo.lastModified() > fName.lastModified())) {
      return;
    }
    final Job job = CompileFile.compile(getFile(), true);
    if (job != null) {
      try {
        job.schedule();
        job.join();
      } 
      catch (InterruptedException e) {
        e.printStackTrace();
      }
    }
    RefreshUtils.refreshTree(viewer, this);
  }
  public boolean isEvaluateEnabled() {
    return true;
  }
}
