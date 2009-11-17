package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.io.*;
import javax.swing.text.*;
import javax.swing.*;
import javax.swing.border.*;
import javax.swing.event.*;
import java.util.*;

class HiddenTagView extends EditableView implements DocumentListener {
    
    HiddenTagView(Element e) {
        super(e);
        yAlign = 1;
    }
    
    protected Component createComponent() {
        JTextField tf = new JTextField(getElement().getName());
        Document doc = getDocument();
        Font font;
        if (doc instanceof StyledDocument) {
            font = ((StyledDocument)(StyledDocument)doc).getFont(getAttributes());
            tf.setFont(font);
        } else {
            font = tf.getFont();
        }
        tf.getDocument().addDocumentListener(this);
        updateYAlign(font);
        JPanel panel = new JPanel(new BorderLayout());
        panel.setBackground(null);
        if (isEndTag()) {
            panel.setBorder(EndBorder);
        } else {
            panel.setBorder(StartBorder);
        }
        panel.add(tf);
        return panel;
    }
    
    public float getAlignment(int axis) {
        if (axis == View.Y_AXIS) {
            return yAlign;
        }
        return 0.5F;
    }
    
    public float getMinimumSpan(int axis) {
        if (axis == View.X_AXIS && isVisible()) {
            return Math.max(30, super.getPreferredSpan(axis));
        }
        return super.getMinimumSpan(axis);
    }
    
    public float getPreferredSpan(int axis) {
        if (axis == View.X_AXIS && isVisible()) {
            return Math.max(30, super.getPreferredSpan(axis));
        }
        return super.getPreferredSpan(axis);
    }
    
    public float getMaximumSpan(int axis) {
        if (axis == View.X_AXIS && isVisible()) {
            return Math.max(30, super.getMaximumSpan(axis));
        }
        return super.getMaximumSpan(axis);
    }
    
    public void insertUpdate(DocumentEvent e) {
        updateModelFromText();
    }
    
    public void removeUpdate(DocumentEvent e) {
        updateModelFromText();
    }
    
    public void changedUpdate(DocumentEvent e) {
        updateModelFromText();
    }
    
    public void changedUpdate(DocumentEvent e, Shape a, ViewFactory f) {
        if (!isSettingAttributes) {
            setTextFromModel();
        }
    }
    
    void updateYAlign(Font font) {
        Container c = getContainer();
        FontMetrics fm = (c != null) ? c.getFontMetrics(font) : Toolkit.getDefaultToolkit().getFontMetrics(font);
        float h = fm.getHeight();
        float d = fm.getDescent();
        yAlign = (h - d) / h;
    }
    
    void resetBorder() {
        Component comp = getComponent();
        if (comp != null) {
            if (isEndTag()) {
                ((JPanel)(JPanel)comp).setBorder(EndBorder);
            } else {
                ((JPanel)(JPanel)comp).setBorder(StartBorder);
            }
        }
    }
    
    void setTextFromModel() {
        if (SwingUtilities.isEventDispatchThread()) {
            _setTextFromModel();
        } else {
            SwingUtilities.invokeLater(new HiddenTagView$1(this));
        }
    }
    
    void _setTextFromModel() {
        Document doc = getDocument();
        try {
            isSettingAttributes = true;
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readLock();
            }
            JTextComponent text = getTextComponent();
            if (text != null) {
                text.setText(getRepresentedText());
                resetBorder();
                Container host = getContainer();
                if (host != null) {
                    preferenceChanged(this, true, true);
                    host.repaint();
                }
            }
        } finally {
            isSettingAttributes = false;
            if (doc instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)doc).readUnlock();
            }
        }
    }
    
    void updateModelFromText() {
        if (!isSettingAttributes) {
            if (SwingUtilities.isEventDispatchThread()) {
                _updateModelFromText();
            } else {
                SwingUtilities.invokeLater(new HiddenTagView$2(this));
            }
        }
    }
    
    void _updateModelFromText() {
        Document doc = getDocument();
        Object name = getElement().getAttributes().getAttribute(StyleConstants.NameAttribute);
        if ((name instanceof HTML$UnknownTag) && (doc instanceof StyledDocument)) {
            SimpleAttributeSet sas = new SimpleAttributeSet();
            JTextComponent textComponent = getTextComponent();
            if (textComponent != null) {
                String text = textComponent.getText();
                isSettingAttributes = true;
                try {
                    sas.addAttribute(StyleConstants.NameAttribute, new HTML$UnknownTag(text));
                    ((StyledDocument)(StyledDocument)doc).setCharacterAttributes(getStartOffset(), getEndOffset() - getStartOffset(), sas, false);
                } finally {
                    isSettingAttributes = false;
                }
            }
        }
    }
    
    JTextComponent getTextComponent() {
        Component comp = getComponent();
        return (comp == null) ? null : (JTextComponent)(JTextComponent)((Container)(Container)comp).getComponent(0);
    }
    
    String getRepresentedText() {
        String retValue = getElement().getName();
        return (retValue == null) ? "" : retValue;
    }
    
    boolean isEndTag() {
        AttributeSet as = getElement().getAttributes();
        if (as != null) {
            Object end = as.getAttribute(HTML$Attribute.ENDTAG);
            if (end != null && (end instanceof String) && ((String)(String)end).equals("true")) {
                return true;
            }
        }
        return false;
    }
    float yAlign;
    boolean isSettingAttributes;
    static final int circleR = 3;
    static final int circleD = circleR * 2;
    static final int tagSize = 6;
    static final int padding = 3;
    static final Color UnknownTagBorderColor = Color.black;
    static final Border StartBorder = new HiddenTagView$StartTagBorder();
    static final Border EndBorder = new HiddenTagView$EndTagBorder();
    {
    }
    {
    }
}
