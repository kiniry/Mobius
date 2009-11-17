package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;
import javax.swing.UIManager;

public class StyledEditorKit$FontFamilyAction extends StyledEditorKit$StyledTextAction {
    
    public StyledEditorKit$FontFamilyAction(String nm, String family) {
        super(nm);
        this.family = family;
    }
    
    public void actionPerformed(ActionEvent e) {
        JEditorPane editor = getEditor(e);
        if (editor != null) {
            String family = this.family;
            if ((e != null) && (e.getSource() == editor)) {
                String s = e.getActionCommand();
                if (s != null) {
                    family = s;
                }
            }
            if (family != null) {
                MutableAttributeSet attr = new SimpleAttributeSet();
                StyleConstants.setFontFamily(attr, family);
                setCharacterAttributes(editor, attr, false);
            } else {
                UIManager.getLookAndFeel().provideErrorFeedback(editor);
            }
        }
    }
    private String family;
}
