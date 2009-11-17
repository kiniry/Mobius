package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

class DefaultEditorKit$PreviousWordAction extends TextAction {
    
    DefaultEditorKit$PreviousWordAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            int offs = target.getCaretPosition();
            boolean failed = false;
            try {
                Element curPara = Utilities.getParagraphElement(target, offs);
                offs = Utilities.getPreviousWord(target, offs);
                if (offs < curPara.getStartOffset()) {
                    offs = Utilities.getParagraphElement(target, offs).getEndOffset() - 1;
                }
            } catch (BadLocationException bl) {
                if (offs != 0) {
                    offs = 0;
                } else {
                    failed = true;
                }
            }
            if (!failed) {
                if (select) {
                    target.moveCaretPosition(offs);
                } else {
                    target.setCaretPosition(offs);
                }
            } else {
                UIManager.getLookAndFeel().provideErrorFeedback(target);
            }
        }
    }
    private boolean select;
}
