package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.Action;

class DefaultEditorKit$SelectLineAction extends TextAction {
    
    DefaultEditorKit$SelectLineAction() {
        super("select-line");
        start = new DefaultEditorKit$BeginLineAction("pigdog", false);
        end = new DefaultEditorKit$EndLineAction("pigdog", true);
    }
    
    public void actionPerformed(ActionEvent e) {
        start.actionPerformed(e);
        end.actionPerformed(e);
    }
    private Action start;
    private Action end;
}
