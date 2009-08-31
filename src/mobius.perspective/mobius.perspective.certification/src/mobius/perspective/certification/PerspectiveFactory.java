package mobius.perspective.certification;

import org.eclipse.jdt.ui.JavaUI;
import org.eclipse.ui.IFolderLayout;
import org.eclipse.ui.IPageLayout;
import org.eclipse.ui.IPerspectiveFactory;
import org.eclipse.ui.console.IConsoleConstants;

/**
 * This class is used to implement the perspective layout.
 * 
 * @author J. Charles (julien.charles@inria.fr)
 */
public class PerspectiveFactory implements IPerspectiveFactory {
  /** represents the number two third (2/3). */
  private static final float twoThird = 0.66f;
  /** {@inheritDoc} */
  public void createInitialLayout(final IPageLayout layout) {
    // Get the editor area.
    final String editorArea = layout.getEditorArea();
    
    // Top left: Resource Navigator view and Bookmarks view placeholder
    final IFolderLayout left = layout.createFolder("topLeft", IPageLayout.LEFT, 
                                                   0.25f, editorArea);
    left.addView(JavaUI.ID_PACKAGES);
    left.addPlaceholder(IPageLayout.ID_BOOKMARKS);
    

    // Bottom right: Task List view
    layout.addView(IConsoleConstants.ID_CONSOLE_VIEW, IPageLayout.BOTTOM, 
                   twoThird, editorArea);
      
    // Bottom left: Outline view and Property Sheet view
    final IFolderLayout right = layout.createFolder("right", IPageLayout.RIGHT, 
                                                    0.65f, editorArea);
    right.addView(IPageLayout.ID_OUTLINE);
    right.addView(IPageLayout.ID_PROP_SHEET);
    right.addView("CoqMobiusUI.view");
  }

}
