package mobius.prover.gui.jobs;

import mobius.prover.gui.editor.IColorConstants;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;

public class ToplevelStyleRange extends StyleRange implements IColorConstants {

  public ToplevelStyleRange(int i, int len, Color col) {
    super(i, len, col, WHITE);
    font = JFaceResources.getTextFont();
  }

}
