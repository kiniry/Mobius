package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$BeginAction extends TextAction {
    
    DefaultEditorKit$BeginAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            if (select) {
                target.moveCaretPosition(0);
            } else {
                target.setCaretPosition(0);
            }
        }
    }
    private boolean select;
}
