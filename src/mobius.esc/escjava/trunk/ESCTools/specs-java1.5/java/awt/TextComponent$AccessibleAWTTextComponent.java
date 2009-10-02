package java.awt;

import java.awt.event.*;
import java.text.BreakIterator;
import javax.swing.text.AttributeSet;
import javax.accessibility.*;

public class TextComponent$AccessibleAWTTextComponent extends Component$AccessibleAWTComponent implements AccessibleText, TextListener {
    /*synthetic*/ final TextComponent this$0;
    private static final long serialVersionUID = 3631432373506317811L;
    
    public TextComponent$AccessibleAWTTextComponent(/*synthetic*/ final TextComponent this$0) {
        this.this$0 = this$0;
        super(this$0);
        this$0.addTextListener(this);
    }
    
    public void textValueChanged(TextEvent textEvent) {
        Integer cpos = new Integer(this$0.getCaretPosition());
        firePropertyChange(ACCESSIBLE_TEXT_PROPERTY, null, cpos);
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
        return this$0.getIndexAtPoint(p);
    }
    
    public Rectangle getCharacterBounds(int i) {
        return this$0.getCharacterBounds(i);
    }
    
    public int getCharCount() {
        return this$0.getText().length();
    }
    
    public int getCaretPosition() {
        return this$0.getCaretPosition();
    }
    
    public AttributeSet getCharacterAttribute(int i) {
        return null;
    }
    
    public int getSelectionStart() {
        return this$0.getSelectionStart();
    }
    
    public int getSelectionEnd() {
        return this$0.getSelectionEnd();
    }
    
    public String getSelectedText() {
        String selText = this$0.getSelectedText();
        if (selText == null || selText.equals("")) {
            return null;
        }
        return selText;
    }
    
    public String getAtIndex(int part, int index) {
        if (index < 0 || index >= this$0.getText().length()) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            return this$0.getText().substring(index, index + 1);
        
        case AccessibleText.WORD: 
            {
                String s = this$0.getText();
                BreakIterator words = BreakIterator.getWordInstance();
                words.setText(s);
                int end = words.following(index);
                return s.substring(words.previous(), end);
            }
        
        case AccessibleText.SENTENCE: 
            {
                String s = this$0.getText();
                BreakIterator sentence = BreakIterator.getSentenceInstance();
                sentence.setText(s);
                int end = sentence.following(index);
                return s.substring(sentence.previous(), end);
            }
        
        default: 
            return null;
        
        }
    }
    private static final boolean NEXT = true;
    private static final boolean PREVIOUS = false;
    
    private int findWordLimit(int index, BreakIterator words, boolean direction, String s) {
        int last = (direction == NEXT) ? words.following(index) : words.preceding(index);
        int current = (direction == NEXT) ? words.next() : words.previous();
        while (current != BreakIterator.DONE) {
            for (int p = Math.min(last, current); p < Math.max(last, current); p++) {
                if (Character.isLetter(s.charAt(p))) {
                    return last;
                }
            }
            last = current;
            current = (direction == NEXT) ? words.next() : words.previous();
        }
        return BreakIterator.DONE;
    }
    
    public String getAfterIndex(int part, int index) {
        if (index < 0 || index >= this$0.getText().length()) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            if (index + 1 >= this$0.getText().length()) {
                return null;
            }
            return this$0.getText().substring(index + 1, index + 2);
        
        case AccessibleText.WORD: 
            {
                String s = this$0.getText();
                BreakIterator words = BreakIterator.getWordInstance();
                words.setText(s);
                int start = findWordLimit(index, words, NEXT, s);
                if (start == BreakIterator.DONE || start >= s.length()) {
                    return null;
                }
                int end = words.following(start);
                if (end == BreakIterator.DONE || end >= s.length()) {
                    return null;
                }
                return s.substring(start, end);
            }
        
        case AccessibleText.SENTENCE: 
            {
                String s = this$0.getText();
                BreakIterator sentence = BreakIterator.getSentenceInstance();
                sentence.setText(s);
                int start = sentence.following(index);
                if (start == BreakIterator.DONE || start >= s.length()) {
                    return null;
                }
                int end = sentence.following(start);
                if (end == BreakIterator.DONE || end >= s.length()) {
                    return null;
                }
                return s.substring(start, end);
            }
        
        default: 
            return null;
        
        }
    }
    
    public String getBeforeIndex(int part, int index) {
        if (index < 0 || index > this$0.getText().length() - 1) {
            return null;
        }
        switch (part) {
        case AccessibleText.CHARACTER: 
            if (index == 0) {
                return null;
            }
            return this$0.getText().substring(index - 1, index);
        
        case AccessibleText.WORD: 
            {
                String s = this$0.getText();
                BreakIterator words = BreakIterator.getWordInstance();
                words.setText(s);
                int end = findWordLimit(index, words, PREVIOUS, s);
                if (end == BreakIterator.DONE) {
                    return null;
                }
                int start = words.preceding(end);
                if (start == BreakIterator.DONE) {
                    return null;
                }
                return s.substring(start, end);
            }
        
        case AccessibleText.SENTENCE: 
            {
                String s = this$0.getText();
                BreakIterator sentence = BreakIterator.getSentenceInstance();
                sentence.setText(s);
                int end = sentence.following(index);
                end = sentence.previous();
                int start = sentence.previous();
                if (start == BreakIterator.DONE) {
                    return null;
                }
                return s.substring(start, end);
            }
        
        default: 
            return null;
        
        }
    }
}
