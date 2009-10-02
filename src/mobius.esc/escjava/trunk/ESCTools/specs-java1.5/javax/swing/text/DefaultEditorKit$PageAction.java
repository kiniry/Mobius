package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$PageAction extends TextAction {
    
    public DefaultEditorKit$PageAction(String nm, boolean left, boolean select) {
        super(nm);
        this.select = select;
        this.left = left;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            int selectedIndex;
            Rectangle visible = new Rectangle();
            target.computeVisibleRect(visible);
            if (left) {
                visible.x = Math.max(0, visible.x - visible.width);
            } else {
                visible.x += visible.width;
            }
            selectedIndex = target.getCaretPosition();
            if (selectedIndex != -1) {
                if (left) {
                    selectedIndex = target.viewToModel(new Point(visible.x, visible.y));
                } else {
                    selectedIndex = target.viewToModel(new Point(visible.x + visible.width - 1, visible.y + visible.height - 1));
                }
                Document doc = target.getDocument();
                if ((selectedIndex != 0) && (selectedIndex > (doc.getLength() - 1))) {
                    selectedIndex = doc.getLength() - 1;
                } else if (selectedIndex < 0) {
                    selectedIndex = 0;
                }
                if (select) target.moveCaretPosition(selectedIndex); else target.setCaretPosition(selectedIndex);
            }
        }
    }
    private boolean select;
    private boolean left;
}
