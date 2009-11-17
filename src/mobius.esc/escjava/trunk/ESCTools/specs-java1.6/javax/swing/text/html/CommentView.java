package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class CommentView extends HiddenTagView {
    
    CommentView(Element e) {
        super(e);
    }
    
    protected Component createComponent() {
        Container host = getContainer();
        if (host != null && !((JTextComponent)(JTextComponent)host).isEditable()) {
            return null;
        }
        JTextArea ta = new JTextArea(getRepresentedText());
        Document doc = getDocument();
        Font font;
        if (doc instanceof StyledDocument) {
            font = ((StyledDocument)(StyledDocument)doc).getFont(getAttributes());
            ta.setFont(font);
        } else {
            font = ta.getFont();
        }
        updateYAlign(font);
        ta.setBorder(CBorder);
        ta.getDocument().addDocumentListener(this);
        ta.setFocusable(isVisible());
        return ta;
    }
    
    void resetBorder() {
    }
    
    void _updateModelFromText() {
        JTextComponent textC = getTextComponent();
        Document doc = getDocument();
        if (textC != null && doc != null) {
            String text = textC.getText();
            SimpleAttributeSet sas = new SimpleAttributeSet();
            isSettingAttributes = true;
            try {
                sas.addAttribute(HTML$Attribute.COMMENT, text);
                ((StyledDocument)(StyledDocument)doc).setCharacterAttributes(getStartOffset(), getEndOffset() - getStartOffset(), sas, false);
            } finally {
                isSettingAttributes = false;
            }
        }
    }
    
    JTextComponent getTextComponent() {
        return (JTextComponent)(JTextComponent)getComponent();
    }
    
    String getRepresentedText() {
        AttributeSet as = getElement().getAttributes();
        if (as != null) {
            Object comment = as.getAttribute(HTML$Attribute.COMMENT);
            if (comment instanceof String) {
                return (String)(String)comment;
            }
        }
        return "";
    }
    static final Border CBorder = new CommentView$CommentBorder();
    static final int commentPadding = 3;
    static final int commentPaddingD = commentPadding * 3;
    {
    }
}
