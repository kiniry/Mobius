package mobius.directVCGen.ui.poview.tree;

import mobius.directVCGen.ui.poview.Utils;

import org.eclipse.swt.graphics.Image;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.ide.IDE;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;


public class LibFile extends WorkspaceElement implements IShowable {
	IFile file;
	private LibFile(IFile key) {
		super(key);
		file = key;
		
	}

	public WorkspaceElement createChildFromResource(IResource res) {
		return null;
	}

	public void update() {
	}

	public String getName() {
		return file.getName();
	}
	public Image getImage () {
		return Utils.getImage(IMG_LIB);
	}
	
	public void show() {
		try {
			IDE.openEditor(PlatformUI.getWorkbench().getActiveWorkbenchWindow().getActivePage(), file);
		} catch (PartInitException e) {
			e.printStackTrace();
		}
	}

  public static WorkspaceElement createCoqFileOrGoal(IFile f) {
    WorkspaceElement res;
    if (f.getName().startsWith("goal")) {
      return new Goal(f);
    }
    return new LibFile(f);
  }
}
