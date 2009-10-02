package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$DumpModelAction extends TextAction {
    
    DefaultEditorKit$DumpModelAction() {
        super("dump-model");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            Document d = target.getDocument();
            if (d instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)d).dump(System.err);
            }
        }
    }
}
