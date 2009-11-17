package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;
import javax.swing.UIManager;

class StyledEditorKit$StyledInsertBreakAction extends StyledEditorKit$StyledTextAction {
    private SimpleAttributeSet tempSet;
    
    StyledEditorKit$StyledInsertBreakAction() {
        super("insert-break");
    }
    
    public void actionPerformed(ActionEvent e) {
        JEditorPane target = getEditor(e);
        if (target != null) {
            if ((!target.isEditable()) || (!target.isEnabled())) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
                return;
            }
            StyledEditorKit sek = getStyledEditorKit(target);
            if (tempSet != null) {
                tempSet.removeAttributes(tempSet);
            } else {
                tempSet = new SimpleAttributeSet();
            }
            tempSet.addAttributes(sek.getInputAttributes());
            target.replaceSelection("\n");
            MutableAttributeSet ia = sek.getInputAttributes();
            ia.removeAttributes(ia);
            ia.addAttributes(tempSet);
            tempSet.removeAttributes(tempSet);
        } else {
            JTextComponent text = getTextComponent(e);
            if (text != null) {
                if ((!text.isEditable()) || (!text.isEnabled())) {
                    UIManager.getLookAndFeel().provideErrorFeedback(target);
                    return;
                }
                text.replaceSelection("\n");
            }
        }
    }
}
