package mobius.prover.gui.jobs;

import mobius.prover.gui.editor.IColorConstants;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;

/**
 * A style range with a white background.
 * @author J. Charles (julien.charles@gmail.com)
 */
public class ToplevelStyleRange extends StyleRange implements IColorConstants {
  /**
   * Creates a top level style range, a style range with a white background.
   * @param i the starting point of the range
   * @param len the length of the range
   * @param col the foreground color
   */
  public ToplevelStyleRange(final int i, final int len, final Color col) {
    super(i, len, col, WHITE);
    font = JFaceResources.getTextFont();
  }
}
