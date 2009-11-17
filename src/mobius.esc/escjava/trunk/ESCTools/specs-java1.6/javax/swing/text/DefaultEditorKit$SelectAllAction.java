package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$SelectAllAction extends TextAction {
    
    DefaultEditorKit$SelectAllAction() {
        super("select-all");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            Document doc = target.getDocument();
            target.setCaretPosition(0);
            target.moveCaretPosition(doc.getLength());
        }
    }
}
