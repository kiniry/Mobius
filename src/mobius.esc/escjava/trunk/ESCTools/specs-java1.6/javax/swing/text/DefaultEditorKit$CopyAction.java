package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

public class DefaultEditorKit$CopyAction extends TextAction {
    
    public DefaultEditorKit$CopyAction() {
        super("copy-to-clipboard");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.copy();
        }
    }
}
