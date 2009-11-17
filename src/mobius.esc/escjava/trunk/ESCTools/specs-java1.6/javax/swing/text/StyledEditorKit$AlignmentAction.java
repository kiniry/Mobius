package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;

public class StyledEditorKit$AlignmentAction extends StyledEditorKit$StyledTextAction {
    
    public StyledEditorKit$AlignmentAction(String nm, int a) {
        super(nm);
        this.a = a;
    }
    
    public void actionPerformed(ActionEvent e) {
        JEditorPane editor = getEditor(e);
        if (editor != null) {
            int a = this.a;
            if ((e != null) && (e.getSource() == editor)) {
                String s = e.getActionCommand();
                try {
                    a = Integer.parseInt(s, 10);
                } catch (NumberFormatException nfe) {
                }
            }
            MutableAttributeSet attr = new SimpleAttributeSet();
            StyleConstants.setAlignment(attr, a);
            setParagraphAttributes(editor, attr, false);
        }
    }
    private int a;
}
