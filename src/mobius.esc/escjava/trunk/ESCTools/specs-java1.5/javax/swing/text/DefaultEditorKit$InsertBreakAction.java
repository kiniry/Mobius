package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

public class DefaultEditorKit$InsertBreakAction extends TextAction {
    
    public DefaultEditorKit$InsertBreakAction() {
        super("insert-break");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            if ((!target.isEditable()) || (!target.isEnabled())) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
                return;
            }
            target.replaceSelection("\n");
        }
    }
}
