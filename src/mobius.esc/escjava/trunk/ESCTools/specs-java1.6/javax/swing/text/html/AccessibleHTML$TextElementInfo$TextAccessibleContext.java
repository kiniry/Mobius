package javax.swing.text.html;

import java.awt.*;
import java.awt.event.*;
import java.beans.*;
import java.util.*;
import javax.swing.*;
import javax.swing.event.*;
import javax.swing.text.*;
import javax.accessibility.*;
import java.text.BreakIterator;

public class AccessibleHTML$TextElementInfo$TextAccessibleContext extends AccessibleHTML$HTMLAccessibleContext implements AccessibleText {
    /*synthetic*/ final AccessibleHTML$TextElementInfo this$1;
    
    public AccessibleHTML$TextElementInfo$TextAccessibleContext(/*synthetic*/ final AccessibleHTML$TextElementInfo this$1, AccessibleHTML$ElementInfo elementInfo) {
        super(this$1.this$0, elementInfo);
        this.this$1 = this$1;
    }
    
    public AccessibleText getAccessibleText() {
        return this;
    }
    
    public String getAccessibleName() {
        if (AccessibleHTML.access$200(this$1.this$0) != null) {
            return (String)(String)AccessibleHTML.access$200(this$1.this$0).getProperty(Document.TitleProperty);
        } else {
            return null;
        }
    }
    
    public String getAccessibleDescription() {
        return AccessibleHTML.access$300(this$1.this$0).getContentType();
    }
    
    public AccessibleRole getAccessibleRole() {
        return AccessibleRole.TEXT;
    }
    
    public int getIndexAtPoint(Point p) {
        View v = this$1.getView();
        if (v != null) {
            return v.viewToModel(p.x, p.y, getBounds());
        } else {
            return -1;
        }
    }
    
    public Rectangle getCharacterBounds(int i) {
        try {
            return AccessibleHTML.access$300(this$1.this$0).getUI().modelToView(AccessibleHTML.access$300(this$1.this$0), i);
        } catch (BadLocationException e) {
            return null;
        }
    }
    
    public int getCharCount() {
        if (this$1.validateIfNecessary()) {
            Element elem = elementInfo.getElement();
            return elem.getEndOffset() - elem.getStartOffset();
        }
        return 0;
    }
    
    public int getCaretPosition() {
        View v = this$1.getView();
        if (v == null) {
            return -1;
        }
        Container c = v.getContainer();
        if (c == null) {
            return -1;
        }
        if (c instanceof JTextComponent) {
            return ((JTextComponent)(JTextComponent)c).getCaretPosition();
        } else {
            return -1;
        }
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
        if (AccessibleHTML.access$200(this$1.this$0) instanceof AbstractDocument) {
            ((AbstractDocument)(AbstractDocument)AccessibleHTML.access$200(this$1.this$0)).readLock();
        }
        try {
            if (index < 0 || index >= AccessibleHTML.access$200(this$1.this$0).getLength()) {
                return null;
            }
            switch (part) {
            case AccessibleText.CHARACTER: 
                if (index + direction < AccessibleHTML.access$200(this$1.this$0).getLength() && index + direction >= 0) {
                    return AccessibleHTML.access$200(this$1.this$0).getText(index + direction, 1);
                }
                break;
            
            case AccessibleText.WORD: 
            
            case AccessibleText.SENTENCE: 
                AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment seg = getSegmentAt(part, index);
                if (seg != null) {
                    if (direction != 0) {
                        int next;
                        if (direction < 0) {
                            next = seg.modelOffset - 1;
                        } else {
                            next = seg.modelOffset + direction * seg.count;
                        }
                        if (next >= 0 && next <= AccessibleHTML.access$200(this$1.this$0).getLength()) {
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
            if (AccessibleHTML.access$200(this$1.this$0) instanceof AbstractDocument) {
                ((AbstractDocument)(AbstractDocument)AccessibleHTML.access$200(this$1.this$0)).readUnlock();
            }
        }
        return null;
    }
    
    private Element getParagraphElement(int index) {
        if (AccessibleHTML.access$200(this$1.this$0) instanceof PlainDocument) {
            PlainDocument sdoc = (PlainDocument)(PlainDocument)AccessibleHTML.access$200(this$1.this$0);
            return sdoc.getParagraphElement(index);
        } else if (AccessibleHTML.access$200(this$1.this$0) instanceof StyledDocument) {
            StyledDocument sdoc = (StyledDocument)(StyledDocument)AccessibleHTML.access$200(this$1.this$0);
            return sdoc.getParagraphElement(index);
        } else {
            Element para = null;
            for (para = AccessibleHTML.access$200(this$1.this$0).getDefaultRootElement(); !para.isLeaf(); ) {
                int pos = para.getElementIndex(index);
                para = para.getElement(pos);
            }
            if (para == null) {
                return null;
            }
            return para.getParentElement();
        }
    }
    
    private AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment getParagraphElementText(int index) throws BadLocationException {
        Element para = getParagraphElement(index);
        if (para != null) {
            AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment segment = new AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment(this, null);
            try {
                int length = para.getEndOffset() - para.getStartOffset();
                AccessibleHTML.access$200(this$1.this$0).getText(para.getStartOffset(), length, segment);
            } catch (BadLocationException e) {
                return null;
            }
            segment.modelOffset = para.getStartOffset();
            return segment;
        }
        return null;
    }
    
    private AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment getSegmentAt(int part, int index) throws BadLocationException {
        AccessibleHTML$TextElementInfo$TextAccessibleContext$IndexedSegment seg = getParagraphElementText(index);
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
    
    public AttributeSet getCharacterAttribute(int i) {
        if (AccessibleHTML.access$200(this$1.this$0) instanceof StyledDocument) {
            StyledDocument doc = (StyledDocument)(StyledDocument)AccessibleHTML.access$200(this$1.this$0);
            Element elem = doc.getCharacterElement(i);
            if (elem != null) {
                return elem.getAttributes();
            }
        }
        return null;
    }
    
    public int getSelectionStart() {
        return AccessibleHTML.access$300(this$1.this$0).getSelectionStart();
    }
    
    public int getSelectionEnd() {
        return AccessibleHTML.access$300(this$1.this$0).getSelectionEnd();
    }
    
    public String getSelectedText() {
        return AccessibleHTML.access$300(this$1.this$0).getSelectedText();
    }
    
    private String getText(int offset, int length) throws BadLocationException {
        if (AccessibleHTML.access$200(this$1.this$0) != null && AccessibleHTML.access$200(this$1.this$0) instanceof StyledDocument) {
            StyledDocument doc = (StyledDocument)(StyledDocument)AccessibleHTML.access$200(this$1.this$0);
            return AccessibleHTML.access$200(this$1.this$0).getText(offset, length);
        } else {
            return null;
        }
    }
}
