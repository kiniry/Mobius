package javax.swing.text;

import java.io.*;
import java.awt.*;
import java.awt.event.*;
import java.awt.datatransfer.*;
import java.awt.im.InputMethodRequests;
import java.awt.font.TextHitInfo;
import java.text.*;
import java.text.AttributedCharacterIterator.Attribute;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.plaf.*;
import javax.accessibility.*;

class JTextComponent$InputMethodRequestsHandler implements InputMethodRequests, DocumentListener {
    /*synthetic*/ final JTextComponent this$0;
    
    JTextComponent$InputMethodRequestsHandler(/*synthetic*/ final JTextComponent this$0) {
        this.this$0 = this$0;
        
    }
    
    public AttributedCharacterIterator cancelLatestCommittedText(AttributedCharacterIterator$Attribute[] attributes) {
        Document doc = this$0.getDocument();
        if ((doc != null) && (JTextComponent.access$600(this$0) != null) && (!JTextComponent.access$600(this$0).equals(JTextComponent.access$700(this$0)))) {
            try {
                int startIndex = JTextComponent.access$600(this$0).getOffset();
                int endIndex = JTextComponent.access$700(this$0).getOffset();
                String latestCommittedText = doc.getText(startIndex, endIndex - startIndex);
                doc.remove(startIndex, endIndex - startIndex);
                return new AttributedString(latestCommittedText).getIterator();
            } catch (BadLocationException ble) {
            }
        }
        return null;
    }
    
    public AttributedCharacterIterator getCommittedText(int beginIndex, int endIndex, AttributedCharacterIterator$Attribute[] attributes) {
        int composedStartIndex = 0;
        int composedEndIndex = 0;
        if (this$0.composedTextExists()) {
            composedStartIndex = JTextComponent.access$800(this$0).getOffset();
            composedEndIndex = JTextComponent.access$900(this$0).getOffset();
        }
        String committed;
        try {
            if (beginIndex < composedStartIndex) {
                if (endIndex <= composedStartIndex) {
                    committed = this$0.getText(beginIndex, endIndex - beginIndex);
                } else {
                    int firstPartLength = composedStartIndex - beginIndex;
                    committed = this$0.getText(beginIndex, firstPartLength) + this$0.getText(composedEndIndex, endIndex - beginIndex - firstPartLength);
                }
            } else {
                committed = this$0.getText(beginIndex + (composedEndIndex - composedStartIndex), endIndex - beginIndex);
            }
        } catch (BadLocationException ble) {
            throw new IllegalArgumentException("Invalid range");
        }
        return new AttributedString(committed).getIterator();
    }
    
    public int getCommittedTextLength() {
        Document doc = this$0.getDocument();
        int length = 0;
        if (doc != null) {
            length = doc.getLength();
            if (JTextComponent.access$1000(this$0) != null) {
                if (JTextComponent.access$900(this$0) == null || JTextComponent.access$800(this$0) == null) {
                    length -= JTextComponent.access$1000(this$0).length();
                } else {
                    length -= JTextComponent.access$900(this$0).getOffset() - JTextComponent.access$800(this$0).getOffset();
                }
            }
        }
        return length;
    }
    
    public int getInsertPositionOffset() {
        int composedStartIndex = 0;
        int composedEndIndex = 0;
        if (this$0.composedTextExists()) {
            composedStartIndex = JTextComponent.access$800(this$0).getOffset();
            composedEndIndex = JTextComponent.access$900(this$0).getOffset();
        }
        int caretIndex = this$0.getCaretPosition();
        if (caretIndex < composedStartIndex) {
            return caretIndex;
        } else if (caretIndex < composedEndIndex) {
            return composedStartIndex;
        } else {
            return caretIndex - (composedEndIndex - composedStartIndex);
        }
    }
    
    public TextHitInfo getLocationOffset(int x, int y) {
        if (JTextComponent.access$1100(this$0) == null) {
            return null;
        } else {
            Point p = this$0.getLocationOnScreen();
            p.x = x - p.x;
            p.y = y - p.y;
            int pos = this$0.viewToModel(p);
            if ((pos >= JTextComponent.access$800(this$0).getOffset()) && (pos <= JTextComponent.access$900(this$0).getOffset())) {
                return TextHitInfo.leading(pos - JTextComponent.access$800(this$0).getOffset());
            } else {
                return null;
            }
        }
    }
    
    public Rectangle getTextLocation(TextHitInfo offset) {
        Rectangle r;
        try {
            r = this$0.modelToView(this$0.getCaretPosition());
            if (r != null) {
                Point p = this$0.getLocationOnScreen();
                r.translate(p.x, p.y);
            }
        } catch (BadLocationException ble) {
            r = null;
        }
        if (r == null) r = new Rectangle();
        return r;
    }
    
    public AttributedCharacterIterator getSelectedText(AttributedCharacterIterator$Attribute[] attributes) {
        String selection = this$0.getSelectedText();
        if (selection != null) {
            return new AttributedString(selection).getIterator();
        } else {
            return null;
        }
    }
    
    public void changedUpdate(DocumentEvent e) {
        JTextComponent.access$602(this$0, JTextComponent.access$702(this$0, null));
    }
    
    public void insertUpdate(DocumentEvent e) {
        JTextComponent.access$602(this$0, JTextComponent.access$702(this$0, null));
    }
    
    public void removeUpdate(DocumentEvent e) {
        JTextComponent.access$602(this$0, JTextComponent.access$702(this$0, null));
    }
}
