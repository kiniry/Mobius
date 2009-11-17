package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;
import javax.swing.UIManager;

public class StyledEditorKit$FontSizeAction extends StyledEditorKit$StyledTextAction {
    
    public StyledEditorKit$FontSizeAction(String nm, int size) {
        super(nm);
        this.size = size;
    }
    
    public void actionPerformed(ActionEvent e) {
        JEditorPane editor = getEditor(e);
        if (editor != null) {
            int size = this.size;
            if ((e != null) && (e.getSource() == editor)) {
                String s = e.getActionCommand();
                try {
                    size = Integer.parseInt(s, 10);
                } catch (NumberFormatException nfe) {
                }
            }
            if (size != 0) {
                MutableAttributeSet attr = new SimpleAttributeSet();
                StyleConstants.setFontSize(attr, size);
                setCharacterAttributes(editor, attr, false);
            } else {
                UIManager.getLookAndFeel().provideErrorFeedback(editor);
            }
        }
    }
    private int size;
}
