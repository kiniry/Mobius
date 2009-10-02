package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.text.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

public class JTextComponent$AccessibleJTextComponent extends JComponent$AccessibleJComponent implements AccessibleText, CaretListener, DocumentListener, AccessibleAction, AccessibleEditableText {
    /*synthetic*/ final JTextComponent this$0;
    int caretPos;
    Point oldLocationOnScreen;
    
    public JTextComponent$AccessibleJTextComponent(/*synthetic*/ final JTextComponent this$0) {
        this.this$0 = this$0;
        super(this$0);
        Document doc = this$0.getDocument();
        if (doc != null) {
            doc.addDocumentListener(this);
        }
        this$0.addCaretListener(this);
        caretPos = getCaretPosition();
        try {
            oldLocationOnScreen = getLocationOnScreen();
        } catch (IllegalComponentStateException iae) {
        }
        this$0.addComponentListener(new JTextComponent$AccessibleJTextComponent$1(this, this$0));
    }
    
    public void caretUpdate(CaretEvent e) {
        int dot = e.getDot();
        int mark = e.getMark();
        if (caretPos != dot) {
            firePropertyChange(ACCESSIBLE_CARET_PROPERTY, new Integer(caretPos), new Integer(dot));
            caretPos = dot;
            try {
                oldLocationOnScreen = getLocationOnScreen();
            } catch (IllegalComponentStateException iae) {
            }
        }
        if (mark != dot) {
            firePropertyChange(ACCESSIBLE_SELECTION_PROPERTY, null, getSelectedText());
        }
    }
    
    public void insertUpdate(DocumentEvent e) {
        final Integer pos = new Integer(e.getOffset());
        if (SwingUtilities.isEventDispatchThread()) {
            firePropertyChange(ACCESSIBLE_TEXT_PROPERTY, null, pos);
        } else {
            Runnable doFire = new JTextComponent$AccessibleJTextComponent$2(this, pos);
            SwingUtilities.invokeLater(doFire);
        }
    }
    
    public void removeUpdate(DocumentEvent e) {
        final Integer pos = new Integer(e.getOffset());
        if (SwingUtilities.isEventDispatchThread()) {
            firePropertyChange(ACCESSIBLE_TEXT_PROPERTY, null, pos);
        } else {
            Runnable doFire = new JTextComponent$AccessibleJTextComponent$3(this, pos);
            SwingUtilities.invokeLater(doFire);
        }
    }
    
    public void changedUpdate(DocumentEvent e) {
        final Integer pos = new Integer(e.getOffset());
        if (SwingUtilities.isEventDispatchThread()) {
            firePropertyChange(ACCESSIBLE_TEXT_PROPERTY, null, pos);
        } else {
            Runnable doFire = new JTextComponent$AccessibleJTextComponent$4(this, pos);
            SwingUtilities.invokeLater(doFire);
        }
    }
    
    public AccessibleStateSet getAccessibleStateSet() {
        AccessibleStateSet states = super.getAccessibleStateSet();
        if (this$0.isEditable()) {
            states.add(AccessibleState.EDITABLE);
        }
        return states;
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TEXT;
    }
    
    public AccessibleText getAccessibleText() {
        return this;
    }
    
    public int getIndexAtPoint(Point p) {
        if (p == null) {
            return -1;
        }
        return this$0.viewToModel(p);
    }
    
    Rectangle getRootEditorRect() {
        Rectangle alloc = this$0.getBounds();
        if ((alloc.width > 0) && (alloc.height > 0)) {
            alloc.x = alloc.y = 0;
            Insets insets = this$0.getInsets();
            alloc.x += insets.left;
            alloc.y += insets.top;
            alloc.width -= insets.left + insets.right;
            alloc.height -= insets.top + insets.bottom;
            return alloc;
        }
        return null;
    }
    
    public Rectangle getCharacterBounds(int i) {
        if (i < 0 || i > JTextComponent.access$000(this$0).getLength() - 1) {
            return null;
        }
        TextUI ui = this$0.getUI();
        if (ui == null) {
            return null;
        }
        Rectangle rect = null;
        Rectangle alloc = getRootEditorRect();
        if (alloc == null) {
            return null;
        }
        if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
            ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readLock();
        }
        try {
            View rootView = ui.getRootView(this$0);
            if (rootView != null) {
                rootView.setSize(alloc.width, alloc.height);
                Shape bounds = rootView.modelToView(i, Position$Bias.Forward, i + 1, Position$Bias.Backward, alloc);
                rect = (bounds instanceof Rectangle) ? (Rectangle)(Rectangle)bounds : bounds.getBounds();
            }
        } catch (BadLocationException e) {
        } finally {
            if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readUnlock();
            }
        }
        return rect;
    }
    
    public int getCharCount() {
        return JTextComponent.access$000(this$0).getLength();
    }
    
    public int getCaretPosition() {
        return this$0.getCaretPosition();
    }
    
    public AttributeSet getCharacterAttribute(int i) {
        Element e = null;
        if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
            ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readLock();
        }
        try {
            for (e = JTextComponent.access$000(this$0).getDefaultRootElement(); !e.isLeaf(); ) {
                int index = e.getElementIndex(i);
                e = e.getElement(index);
            }
        } finally {
            if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readUnlock();
            }
        }
        return e.getAttributes();
    }
    
    public int getSelectionStart() {
        return this$0.getSelectionStart();
    }
    
    public int getSelectionEnd() {
        return this$0.getSelectionEnd();
    }
    
    public String getSelectedText() {
        return this$0.getSelectedText();
    }
    {
    }
    
    public String getAtIndex(int part, int index) {
        return getAtIndex(part, index, 0);
    }
    
    public String getAfterIndex(int part, int index) {
        return getAtIndex(part, index, 1);
    }
    
    public String getBeforeIndex(int part, int index) {
        return getAtIndex(part, index, -1);
    }
    
    private String getAtIndex(int part, int index, int direction) {
        if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
            ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readLock();
        }
        try {
            if (index < 0 || index >= JTextComponent.access$000(this$0).getLength()) {
                return null;
            }
            switch (part) {
            case AccessibleText.CHARACTER: 
                if (index + direction < JTextComponent.access$000(this$0).getLength() && index + direction >= 0) {
                    return JTextComponent.access$000(this$0).getText(index + direction, 1);
                }
                break;
            
            case AccessibleText.WORD: 
            
            case AccessibleText.SENTENCE: 
                JTextComponent$AccessibleJTextComponent$IndexedSegment seg = getSegmentAt(part, index);
                if (seg != null) {
                    if (direction != 0) {
                        int next;
                        if (direction < 0) {
                            next = seg.modelOffset - 1;
                        } else {
                            next = seg.modelOffset + direction * seg.count;
                        }
                        if (next >= 0 && next <= JTextComponent.access$000(this$0).getLength()) {
                            seg = getSegmentAt(part, next);
                        } else {
                            seg = null;
                        }
                    }
                    if (seg != null) {
                        return new String(seg.array, seg.offset, seg.count);
                    }
                }
                break;
            
            default: 
                break;
            
            }
        } catch (BadLocationException e) {
        } finally {
            if (JTextComponent.access$000(this$0) instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)JTextComponent.access$000(this$0)).readUnlock();
            }
        }
        return null;
    }
    
    private Element getParagraphElement(int index) {
        if (JTextComponent.access$000(this$0) instanceof PlainDocument) {
            PlainDocument sdoc = (PlainDocument)(PlainDocument)JTextComponent.access$000(this$0);
            return sdoc.getParagraphElement(index);
        } else if (JTextComponent.access$000(this$0) instanceof StyledDocument) {
            StyledDocument sdoc = (StyledDocument)(StyledDocument)JTextComponent.access$000(this$0);
            return sdoc.getParagraphElement(index);
        } else {
            Element para = null;
            for (para = JTextComponent.access$000(this$0).getDefaultRootElement(); !para.isLeaf(); ) {
                int pos = para.getElementIndex(index);
                para = para.getElement(pos);
            }
            if (para == null) {
                return null;
            }
            return para.getParentElement();
        }
    }
    
    private JTextComponent$AccessibleJTextComponent$IndexedSegment getParagraphElementText(int index) throws BadLocationException {
        Element para = getParagraphElement(index);
        if (para != null) {
            JTextComponent$AccessibleJTextComponent$IndexedSegment segment = new JTextComponent$AccessibleJTextComponent$IndexedSegment(this, null);
            try {
                int length = para.getEndOffset() - para.getStartOffset();
                JTextComponent.access$000(this$0).getText(para.getStartOffset(), length, segment);
            } catch (BadLocationException e) {
                return null;
            }
            segment.modelOffset = para.getStartOffset();
            return segment;
        }
        return null;
    }
    
    private JTextComponent$AccessibleJTextComponent$IndexedSegment getSegmentAt(int part, int index) throws BadLocationException {
        JTextComponent$AccessibleJTextComponent$IndexedSegment seg = getParagraphElementText(index);
        if (seg == null) {
            return null;
        }
        BreakIterator iterator;
        switch (part) {
        case AccessibleText.WORD: 
            iterator = BreakIterator.getWordInstance(getLocale());
            break;
        
        case AccessibleText.SENTENCE: 
            iterator = BreakIterator.getSentenceInstance(getLocale());
            break;
        
        default: 
            return null;
        
        }
        seg.first();
        iterator.setText(seg);
        int end = iterator.following(index - seg.modelOffset + seg.offset);
        if (end == BreakIterator.DONE) {
            return null;
        }
        if (end > seg.offset + seg.count) {
            return null;
        }
        int begin = iterator.previous();
        if (begin == BreakIterator.DONE || begin >= seg.offset + seg.count) {
            return null;
        }
        seg.modelOffset = seg.modelOffset + begin - seg.offset;
        seg.offset = begin;
        seg.count = end - begin;
        return seg;
    }
    
    public AccessibleEditableText getAccessibleEditableText() {
        return this;
    }
    
    public void setTextContents(String s) {
        this$0.setText(s);
    }
    
    public void insertTextAtIndex(int index, String s) {
        Document doc = this$0.getDocument();
        if (doc != null) {
            try {
                if (s != null && s.length() > 0) {
                    boolean composedTextSaved = JTextComponent.access$200(this$0, index);
                    doc.insertString(index, s, null);
                    if (composedTextSaved) {
                        JTextComponent.access$300(this$0);
                    }
                }
            } catch (BadLocationException e) {
                UIManager.getLookAndFeel().provideErrorFeedback(this$0);
            }
        }
    }
    
    public String getTextRange(int startIndex, int endIndex) {
        String txt = null;
        int p0 = Math.min(startIndex, endIndex);
        int p1 = Math.max(startIndex, endIndex);
        if (p0 != p1) {
            try {
                Document doc = this$0.getDocument();
                txt = doc.getText(p0, p1 - p0);
            } catch (BadLocationException e) {
                throw new IllegalArgumentException(e.getMessage());
            }
        }
        return txt;
    }
    
    public void delete(int startIndex, int endIndex) {
        if (this$0.isEditable() && isEnabled()) {
            try {
                int p0 = Math.min(startIndex, endIndex);
                int p1 = Math.max(startIndex, endIndex);
                if (p0 != p1) {
                    Document doc = this$0.getDocument();
                    doc.remove(p0, p1 - p0);
                }
            } catch (BadLocationException e) {
            }
        } else {
            UIManager.getLookAndFeel().provideErrorFeedback(this$0);
        }
    }
    
    public void cut(int startIndex, int endIndex) {
        selectText(startIndex, endIndex);
        this$0.cut();
    }
    
    public void paste(int startIndex) {
        this$0.setCaretPosition(startIndex);
        this$0.paste();
    }
    
    public void replaceText(int startIndex, int endIndex, String s) {
        selectText(startIndex, endIndex);
        this$0.replaceSelection(s);
    }
    
    public void selectText(int startIndex, int endIndex) {
        this$0.select(startIndex, endIndex);
    }
    
    public void setAttributes(int startIndex, int endIndex, AttributeSet as) {
        Document doc = this$0.getDocument();
        if (doc != null && doc instanceof StyledDocument) {
            StyledDocument sDoc = (StyledDocument)(StyledDocument)doc;
            int offset = startIndex;
            int length = endIndex - startIndex;
            sDoc.setCharacterAttributes(offset, length, as, true);
        }
    }
    
    public AccessibleAction getAccessibleAction() {
        return this;
    }
    
    public int getAccessibleActionCount() {
        Action[] actions = this$0.getActions();
        return actions.length;
    }
    
    public String getAccessibleActionDescription(int i) {
        Action[] actions = this$0.getActions();
        if (i < 0 || i >= actions.length) {
            return null;
        }
        return (String)(String)actions[i].getValue(Action.NAME);
    }
    
    public boolean doAccessibleAction(int i) {
        Action[] actions = this$0.getActions();
        if (i < 0 || i >= actions.length) {
            return false;
        }
        ActionEvent ae = new ActionEvent(this$0, ActionEvent.ACTION_PERFORMED, null, EventQueue.getMostRecentEventTime(), JTextComponent.access$400(this$0));
        actions[i].actionPerformed(ae);
        return true;
    }
}
