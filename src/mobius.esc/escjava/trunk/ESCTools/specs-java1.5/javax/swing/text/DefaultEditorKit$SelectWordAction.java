package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.Action;

class DefaultEditorKit$SelectWordAction extends TextAction {
    
    DefaultEditorKit$SelectWordAction() {
        super("select-word");
        start = new DefaultEditorKit$BeginWordAction("pigdog", false);
        end = new DefaultEditorKit$EndWordAction("pigdog", true);
    }
    
    public void actionPerformed(ActionEvent e) {
        start.actionPerformed(e);
        end.actionPerformed(e);
    }
    private Action start;
    private Action end;
}
