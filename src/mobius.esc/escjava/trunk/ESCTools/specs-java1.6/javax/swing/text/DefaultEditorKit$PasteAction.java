package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

public class DefaultEditorKit$PasteAction extends TextAction {
    
    public DefaultEditorKit$PasteAction() {
        super("paste-from-clipboard");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.paste();
        }
    }
}
