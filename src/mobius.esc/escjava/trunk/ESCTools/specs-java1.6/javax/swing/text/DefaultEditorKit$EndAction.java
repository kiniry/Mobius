package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$EndAction extends TextAction {
    
    DefaultEditorKit$EndAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            Document doc = target.getDocument();
            int dot = doc.getLength();
            if (select) {
                target.moveCaretPosition(dot);
            } else {
                target.setCaretPosition(dot);
            }
        }
    }
    private boolean select;
}
