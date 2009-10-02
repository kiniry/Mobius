package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

class DefaultEditorKit$BeginWordAction extends TextAction {
    
    DefaultEditorKit$BeginWordAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            try {
                int offs = target.getCaretPosition();
                int begOffs = Utilities.getWordStart(target, offs);
                if (select) {
                    target.moveCaretPosition(begOffs);
                } else {
                    target.setCaretPosition(begOffs);
                }
            } catch (BadLocationException bl) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
            }
        }
    }
    private boolean select;
}
