package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.ActionEvent;
import javax.swing.event.*;
import javax.swing.JEditorPane;

public abstract class StyledEditorKit$StyledTextAction extends TextAction {
    
    public StyledEditorKit$StyledTextAction(String nm) {
        super(nm);
    }
    
    protected final JEditorPane getEditor(ActionEvent e) {
        JTextComponent tcomp = getTextComponent(e);
        if (tcomp instanceof JEditorPane) {
            return (JEditorPane)(JEditorPane)tcomp;
        }
        return null;
    }
    
    protected final StyledDocument getStyledDocument(JEditorPane e) {
        Document d = e.getDocument();
        if (d instanceof StyledDocument) {
            return (StyledDocument)(StyledDocument)d;
        }
        throw new IllegalArgumentException("document must be StyledDocument");
    }
    
    protected final StyledEditorKit getStyledEditorKit(JEditorPane e) {
        EditorKit k = e.getEditorKit();
        if (k instanceof StyledEditorKit) {
            return (StyledEditorKit)(StyledEditorKit)k;
        }
        throw new IllegalArgumentException("EditorKit must be StyledEditorKit");
    }
    
    protected final void setCharacterAttributes(JEditorPane editor, AttributeSet attr, boolean replace) {
        int p0 = editor.getSelectionStart();
        int p1 = editor.getSelectionEnd();
        if (p0 != p1) {
            StyledDocument doc = getStyledDocument(editor);
            doc.setCharacterAttributes(p0, p1 - p0, attr, replace);
        }
        StyledEditorKit k = getStyledEditorKit(editor);
        MutableAttributeSet inputAttributes = k.getInputAttributes();
        if (replace) {
            inputAttributes.removeAttributes(inputAttributes);
        }
        inputAttributes.addAttributes(attr);
    }
    
    protected final void setParagraphAttributes(JEditorPane editor, AttributeSet attr, boolean replace) {
        int p0 = editor.getSelectionStart();
        int p1 = editor.getSelectionEnd();
        StyledDocument doc = getStyledDocument(editor);
        doc.setParagraphAttributes(p0, p1 - p0, attr, replace);
    }
}
