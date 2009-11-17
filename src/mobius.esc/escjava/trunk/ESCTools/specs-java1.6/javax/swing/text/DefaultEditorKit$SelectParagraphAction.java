package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.Action;

class DefaultEditorKit$SelectParagraphAction extends TextAction {
    
    DefaultEditorKit$SelectParagraphAction() {
        super("select-paragraph");
        start = new DefaultEditorKit$BeginParagraphAction("pigdog", false);
        end = new DefaultEditorKit$EndParagraphAction("pigdog", true);
    }
    
    public void actionPerformed(ActionEvent e) {
        start.actionPerformed(e);
        end.actionPerformed(e);
    }
    private Action start;
    private Action end;
}
