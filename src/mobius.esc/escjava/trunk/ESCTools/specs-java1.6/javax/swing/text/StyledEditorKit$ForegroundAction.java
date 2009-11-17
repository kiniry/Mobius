package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;
import javax.swing.UIManager;

public class StyledEditorKit$ForegroundAction extends StyledEditorKit$StyledTextAction {
    
    public StyledEditorKit$ForegroundAction(String nm, Color fg) {
        super(nm);
        this.fg = fg;
    }
    
    public void actionPerformed(ActionEvent e) {
        JEditorPane editor = getEditor(e);
        if (editor != null) {
            Color fg = this.fg;
            if ((e != null) && (e.getSource() == editor)) {
                String s = e.getActionCommand();
                try {
                    fg = Color.decode(s);
                } catch (NumberFormatException nfe) {
                }
            }
            if (fg != null) {
                MutableAttributeSet attr = new SimpleAttributeSet();
                StyleConstants.setForeground(attr, fg);
                setCharacterAttributes(editor, attr, false);
            } else {
                UIManager.getLookAndFeel().provideErrorFeedback(editor);
            }
        }
    }
    private Color fg;
}
