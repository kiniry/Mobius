package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;

class DefaultEditorKit$UnselectAction extends TextAction {
    
    DefaultEditorKit$UnselectAction() {
        super("unselect");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            target.setCaretPosition(target.getCaretPosition());
        }
    }
}
