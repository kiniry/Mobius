package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.SwingConstants;

class DefaultEditorKit$NextVisualPositionAction extends TextAction {
    
    DefaultEditorKit$NextVisualPositionAction(String nm, boolean select, int direction) {
        super(nm);
        this.select = select;
        this.direction = direction;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            Caret caret = target.getCaret();
            DefaultCaret bidiCaret = (caret instanceof DefaultCaret) ? (DefaultCaret)(DefaultCaret)caret : null;
            int dot = caret.getDot();
            Position$Bias[] bias = new Position$Bias[1];
            Point magicPosition = caret.getMagicCaretPosition();
            try {
                if (magicPosition == null && (direction == SwingConstants.NORTH || direction == SwingConstants.SOUTH)) {
                    Rectangle r = (bidiCaret != null) ? target.getUI().modelToView(target, dot, bidiCaret.getDotBias()) : target.modelToView(dot);
                    magicPosition = new Point(r.x, r.y);
                }
                NavigationFilter filter = target.getNavigationFilter();
                if (filter != null) {
                    dot = filter.getNextVisualPositionFrom(target, dot, (bidiCaret != null) ? bidiCaret.getDotBias() : Position$Bias.Forward, direction, bias);
                } else {
                    dot = target.getUI().getNextVisualPositionFrom(target, dot, (bidiCaret != null) ? bidiCaret.getDotBias() : Position$Bias.Forward, direction, bias);
                }
                if (bias[0] == null) {
                    bias[0] = Position$Bias.Forward;
                }
                if (bidiCaret != null) {
                    if (select) {
                        bidiCaret.moveDot(dot, bias[0]);
                    } else {
                        bidiCaret.setDot(dot, bias[0]);
                    }
                } else {
                    if (select) {
                        caret.moveDot(dot);
                    } else {
                        caret.setDot(dot);
                    }
                }
                if (magicPosition != null && (direction == SwingConstants.NORTH || direction == SwingConstants.SOUTH)) {
                    target.getCaret().setMagicCaretPosition(magicPosition);
                }
            } catch (BadLocationException ex) {
            }
        }
    }
    private boolean select;
    private int direction;
}
