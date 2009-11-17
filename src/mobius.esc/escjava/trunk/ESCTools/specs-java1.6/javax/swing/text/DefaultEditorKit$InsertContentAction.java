package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

public class DefaultEditorKit$InsertContentAction extends TextAction {
    
    public DefaultEditorKit$InsertContentAction() {
        super("insert-content");
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if ((target != null) && (e != null)) {
            if ((!target.isEditable()) || (!target.isEnabled())) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
                return;
            }
            String content = e.getActionCommand();
            if (content != null) {
                target.replaceSelection(content);
            } else {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
            }
        }
    }
}
