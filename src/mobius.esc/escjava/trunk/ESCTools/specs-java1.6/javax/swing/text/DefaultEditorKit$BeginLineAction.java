package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

class DefaultEditorKit$BeginLineAction extends TextAction {
    
    DefaultEditorKit$BeginLineAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            try {
                int offs = target.getCaretPosition();
                int begOffs = Utilities.getRowStart(target, offs);
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
