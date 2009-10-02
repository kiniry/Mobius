package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.SwingConstants;

class DefaultEditorKit$VerticalPageAction extends TextAction {
    
    public DefaultEditorKit$VerticalPageAction(String nm, int direction, boolean select) {
        super(nm);
        this.select = select;
        this.direction = direction;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            Rectangle visible = target.getVisibleRect();
            Rectangle newVis = new Rectangle(visible);
            int selectedIndex = target.getCaretPosition();
            int scrollAmount = target.getScrollableBlockIncrement(visible, SwingConstants.VERTICAL, direction);
            int initialY = visible.y;
            Caret caret = target.getCaret();
            Point magicPosition = caret.getMagicCaretPosition();
            int yOffset;
            if (selectedIndex != -1) {
                try {
                    Rectangle dotBounds = target.modelToView(selectedIndex);
                    int x = (magicPosition != null) ? magicPosition.x : dotBounds.x;
                    int h = dotBounds.height;
                    yOffset = direction * (int)Math.ceil(scrollAmount / (double)h) * h;
                    newVis.y = constrainY(target, initialY + yOffset, yOffset);
                    int newIndex;
                    if (visible.contains(dotBounds.x, dotBounds.y)) {
                        newIndex = target.viewToModel(new Point(x, constrainY(target, dotBounds.y + yOffset, 0)));
                    } else {
                        if (direction == -1) {
                            newIndex = target.viewToModel(new Point(x, newVis.y));
                        } else {
                            newIndex = target.viewToModel(new Point(x, newVis.y + visible.height));
                        }
                    }
                    newIndex = constrainOffset(target, newIndex);
                    if (newIndex != selectedIndex) {
                        adjustScrollIfNecessary(target, newVis, initialY, newIndex);
                        if (select) {
                            target.moveCaretPosition(newIndex);
                        } else {
                            target.setCaretPosition(newIndex);
                        }
                    }
                } catch (BadLocationException ble) {
                }
            } else {
                yOffset = direction * scrollAmount;
                newVis.y = constrainY(target, initialY + yOffset, yOffset);
            }
            if (magicPosition != null) {
                caret.setMagicCaretPosition(magicPosition);
            }
            target.scrollRectToVisible(newVis);
        }
    }
    
    private int constrainY(JTextComponent target, int y, int vis) {
        if (y < 0) {
            y = 0;
        } else if (y + vis > target.getHeight()) {
            y = Math.max(0, target.getHeight() - vis);
        }
        return y;
    }
    
    private int constrainOffset(JTextComponent text, int offset) {
        Document doc = text.getDocument();
        if ((offset != 0) && (offset > doc.getLength())) {
            offset = doc.getLength();
        }
        if (offset < 0) {
            offset = 0;
        }
        return offset;
    }
    
    private void adjustScrollIfNecessary(JTextComponent text, Rectangle visible, int initialY, int index) {
        try {
            Rectangle dotBounds = text.modelToView(index);
            if (dotBounds.y < visible.y || (dotBounds.y > (visible.y + visible.height)) || (dotBounds.y + dotBounds.height) > (visible.y + visible.height)) {
                int y;
                if (dotBounds.y < visible.y) {
                    y = dotBounds.y;
                } else {
                    y = dotBounds.y + dotBounds.height - visible.height;
                }
                if ((direction == -1 && y < initialY) || (direction == 1 && y > initialY)) {
                    visible.y = y;
                }
            }
        } catch (BadLocationException ble) {
        }
    }
    private boolean select;
    private int direction;
}
