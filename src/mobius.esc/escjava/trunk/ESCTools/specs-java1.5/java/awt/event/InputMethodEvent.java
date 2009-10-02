package java.awt.event;

import java.awt.AWTEvent;
import java.awt.Component;
import java.awt.EventQueue;
import java.awt.font.TextHitInfo;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.text.AttributedCharacterIterator;
import java.text.CharacterIterator;

public class InputMethodEvent extends AWTEvent {
    private static final long serialVersionUID = 4727190874778922661L;
    public static final int INPUT_METHOD_FIRST = 1100;
    public static final int INPUT_METHOD_TEXT_CHANGED = INPUT_METHOD_FIRST;
    public static final int CARET_POSITION_CHANGED = INPUT_METHOD_FIRST + 1;
    public static final int INPUT_METHOD_LAST = INPUT_METHOD_FIRST + 1;
    long when;
    private transient AttributedCharacterIterator text;
    private transient int committedCharacterCount;
    private transient TextHitInfo caret;
    private transient TextHitInfo visiblePosition;
    
    public InputMethodEvent(Component source, int id, long when, AttributedCharacterIterator text, int committedCharacterCount, TextHitInfo caret, TextHitInfo visiblePosition) {
        super(source, id);
        if (id < INPUT_METHOD_FIRST || id > INPUT_METHOD_LAST) {
            throw new IllegalArgumentException("id outside of valid range");
        }
        if (id == CARET_POSITION_CHANGED && text != null) {
            throw new IllegalArgumentException("text must be null for CARET_POSITION_CHANGED");
        }
        this.when = when;
        this.text = text;
        int textLength = 0;
        if (text != null) {
            textLength = text.getEndIndex() - text.getBeginIndex();
        }
        if (committedCharacterCount < 0 || committedCharacterCount > textLength) {
            throw new IllegalArgumentException("committedCharacterCount outside of valid range");
        }
        this.committedCharacterCount = committedCharacterCount;
        this.caret = caret;
        this.visiblePosition = visiblePosition;
    }
    
    public InputMethodEvent(Component source, int id, AttributedCharacterIterator text, int committedCharacterCount, TextHitInfo caret, TextHitInfo visiblePosition) {
        this(source, id, EventQueue.getMostRecentEventTime(), text, committedCharacterCount, caret, visiblePosition);
    }
    
    public InputMethodEvent(Component source, int id, TextHitInfo caret, TextHitInfo visiblePosition) {
        this(source, id, EventQueue.getMostRecentEventTime(), null, 0, caret, visiblePosition);
    }
    
    public AttributedCharacterIterator getText() {
        return text;
    }
    
    public int getCommittedCharacterCount() {
        return committedCharacterCount;
    }
    
    public TextHitInfo getCaret() {
        return caret;
    }
    
    public TextHitInfo getVisiblePosition() {
        return visiblePosition;
    }
    
    public void consume() {
        consumed = true;
    }
    
    public boolean isConsumed() {
        return consumed;
    }
    
    public long getWhen() {
        return when;
    }
    
    public String paramString() {
        String typeStr;
        switch (id) {
        case INPUT_METHOD_TEXT_CHANGED: 
            typeStr = "INPUT_METHOD_TEXT_CHANGED";
            break;
        
        case CARET_POSITION_CHANGED: 
            typeStr = "CARET_POSITION_CHANGED";
            break;
        
        default: 
            typeStr = "unknown type";
        
        }
        String textString;
        if (text == null) {
            textString = "no text";
        } else {
            StringBuffer textBuffer = new StringBuffer("\"");
            int committedCharacterCount = this.committedCharacterCount;
            char c = text.first();
            while (committedCharacterCount-- > 0) {
                textBuffer.append(c);
                c = text.next();
            }
            textBuffer.append("\" + \"");
            while (c != CharacterIterator.DONE) {
                textBuffer.append(c);
                c = text.next();
            }
            textBuffer.append("\"");
            textString = textBuffer.toString();
        }
        String countString = committedCharacterCount + " characters committed";
        String caretString;
        if (caret == null) {
            caretString = "no caret";
        } else {
            caretString = "caret: " + caret.toString();
        }
        String visiblePositionString;
        if (visiblePosition == null) {
            visiblePositionString = "no visible position";
        } else {
            visiblePositionString = "visible position: " + visiblePosition.toString();
        }
        return typeStr + ", " + textString + ", " + countString + ", " + caretString + ", " + visiblePositionString;
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        if (when == 0) {
            when = EventQueue.getMostRecentEventTime();
        }
    }
}
