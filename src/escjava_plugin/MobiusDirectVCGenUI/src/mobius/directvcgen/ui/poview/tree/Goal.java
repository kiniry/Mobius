package mobius.directvcgen.ui.poview.tree;

import java.io.File;

import mobius.directvcgen.ui.poview.util.RefreshUtils;
import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;
import mobius.prover.gui.popup.CompileFile;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;

/**
 * This node represents a goal that has to be proved.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class Goal extends UnknownFile implements IShowable {
  /** the name of the goal file, most likely: <code>goal##.v</code>. */
  private final File fName;
  /** the name of the compiled goal file, most likely: <code>goal##.vo</code>. */
  private final File fNameVo;
  /** the caption that should be shown: <code>Goal ##</code>. */
  private final String fCaption;

  
  /**
   * Initialize a goal from a goal file.
   * @param file the goal file.
   */
  Goal(final IFile file) {
    super(file);
    final String tmp = file.getRawLocation().toString();
    final String name = file.getName();
    if (!name.startsWith("goal") || !name.endsWith(".v")) {
      throw new IllegalArgumentException("The file name must be of the form goal##.v, " +
                                         "not " + name);
    }
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
      return EImages.GOAL_SOLVED.getImg();
    }
    else {
      return EImages.GOAL.getImg();
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
  
  /** {@inheritDoc}  */
  public boolean isEvaluateEnabled() {
    return true;
  }
}
