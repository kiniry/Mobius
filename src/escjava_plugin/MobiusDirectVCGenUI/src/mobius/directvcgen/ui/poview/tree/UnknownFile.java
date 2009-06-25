package mobius.directvcgen.ui.poview.tree;

import mobius.directvcgen.ui.poview.util.ImagesUtils.EImages;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.IEditorDescriptor;
import org.eclipse.ui.IWorkbench;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;
/**
 * A node representing a file of any type.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class UnknownFile extends AWorkspaceElement implements IShowable {
  /** the file that this node represents. */
  private final IFile fFile;
  /** the default image representing the file. */
  private final Image fImg;
  
  /**
   * Creates a node representing a file.
   * @param file the file associated with this node.
   */
  UnknownFile(final IFile file) {
    super(file);
    fFile = file;
    final IEditorDescriptor edit = IDE.getDefaultEditor(getFile());
    if (edit == null) {
      fImg = EImages.UNKNOWN.getImg();
    }
    else {
      fImg = edit.getImageDescriptor().createImage();
    }

    
  }

  /** {@inheritDoc} */
  public AWorkspaceElement createChildFromResource(final IResource res) {
    return null;
  }

  /** {@inheritDoc} */
  public void update() {
  }
  
  /** {@inheritDoc} */
  public String getName() {
    return fFile.getName();
  }
  
  
  /** {@inheritDoc} */
  public Image getImage () {
    return fImg;
  }
  
  
  /** {@inheritDoc} */
  public void show() {
    try {
      final IWorkbench bench = PlatformUI.getWorkbench();
      final IWorkbenchPage page = bench.getActiveWorkbenchWindow().getActivePage(); 
      IDE.openEditor(page, fFile);
    } 
    catch (PartInitException e) {
      e.printStackTrace();
    }
  }
  
  /** {@inheritDoc} */
  public void compile(final TreeViewer viewer) { }
  
  /**
   * Returns the file associated with this node.
   * @return never null
   */
  public final IFile getFile() {
    return fFile;
  }
  
  /** {@inheritDoc} */
  public boolean isEvaluateEnabled() {
    return false;
  }
  

}
