package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

public class DefaultEditorKit$CutAction extends TextAction {
    
    public DefaultEditorKit$CutAction() {
        super("cut-to-clipboard");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.cut();
        }
    }
}
