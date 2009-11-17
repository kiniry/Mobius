package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

class DefaultEditorKit$EndWordAction extends TextAction {
    
    DefaultEditorKit$EndWordAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            try {
                int offs = target.getCaretPosition();
                int endOffs = Utilities.getWordEnd(target, offs);
                if (select) {
                    target.moveCaretPosition(endOffs);
                } else {
                    target.setCaretPosition(endOffs);
                }
            } catch (BadLocationException bl) {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
            }
        }
    }
    private boolean select;
}
