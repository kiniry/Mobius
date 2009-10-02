package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

public class DefaultEditorKit$InsertTabAction extends TextAction {
    
    public DefaultEditorKit$InsertTabAction() {
        super("insert-tab");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            if ((!target.isEditable()) || (!target.isEnabled())) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
                return;
            }
            target.replaceSelection("\t");
        }
    }
}
