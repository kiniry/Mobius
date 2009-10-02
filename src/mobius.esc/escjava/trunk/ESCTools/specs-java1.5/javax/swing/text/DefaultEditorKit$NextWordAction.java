package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import java.text.*;
import javax.swing.UIManager;

class DefaultEditorKit$NextWordAction extends TextAction {
    
    DefaultEditorKit$NextWordAction(String nm, boolean select) {
        super(nm);
        this.select = select;
    }
    
    public void actionPerformed(ActionEvent e) {
        JTextComponent target = getTextComponent(e);
        if (target != null) {
            int offs = target.getCaretPosition();
            boolean failed = false;
            int oldOffs = offs;
            Element curPara = Utilities.getParagraphElement(target, offs);
            try {
                offs = Utilities.getNextWord(target, offs);
                if (offs >= curPara.getEndOffset() && oldOffs != curPara.getEndOffset() - 1) {
                    offs = curPara.getEndOffset() - 1;
                }
            } catch (BadLocationException bl) {
                int end = target.getDocument().getLength();
                if (offs != end) {
                    if (oldOffs != curPara.getEndOffset() - 1) {
                        offs = curPara.getEndOffset() - 1;
                    } else {
                        offs = end;
                    }
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
