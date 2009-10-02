package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$BeginParagraphAction extends TextAction {
    
    DefaultEditorKit$BeginParagraphAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            int offs = target.getCaretPosition();
            Element elem = Utilities.getParagraphElement(target, offs);
            offs = elem.getStartOffset();
            if (select) {
                target.moveCaretPosition(offs);
            } else {
                target.setCaretPosition(offs);
            }
        }
    }
    private boolean select;
}
