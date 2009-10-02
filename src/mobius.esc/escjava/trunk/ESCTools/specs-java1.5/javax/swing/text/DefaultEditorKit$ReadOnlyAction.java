package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$ReadOnlyAction extends TextAction {
    
    DefaultEditorKit$ReadOnlyAction() {
        super("set-read-only");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.setEditable(false);
        }
    }
}
