package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$WritableAction extends TextAction {
    
    DefaultEditorKit$WritableAction() {
        super("set-writable");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.setEditable(true);
        }
    }
}
