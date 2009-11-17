package java.text;

import java.text.CharacterIterator;

final class RuleBasedBreakIterator$SafeCharIterator implements CharacterIterator, Cloneable {
    private CharacterIterator base;
    private int rangeStart;
    private int rangeLimit;
    private int currentIndex;
    
    RuleBasedBreakIterator$SafeCharIterator(CharacterIterator base) {
        
        this.base = base;
        this.rangeStart = base.getBeginIndex();
        this.rangeLimit = base.getEndIndex();
        this.currentIndex = base.getIndex();
    }
    
    public char first() {
        return setIndex(rangeStart);
    }
    
    public char last() {
        return setIndex(rangeLimit - 1);
    }
    
    public char current() {
        if (currentIndex < rangeStart || currentIndex >= rangeLimit) {
            return DONE;
        } else {
            return base.setIndex(currentIndex);
        }
    }
    
    public char next() {
        currentIndex++;
        if (currentIndex >= rangeLimit) {
            currentIndex = rangeLimit;
            return DONE;
        } else {
            return base.setIndex(currentIndex);
        }
    }
    
    public char previous() {
        currentIndex--;
        if (currentIndex < rangeStart) {
            currentIndex = rangeStart;
            return DONE;
        } else {
            return base.setIndex(currentIndex);
        }
    }
    
    public char setIndex(int i) {
        if (i < rangeStart || i > rangeLimit) {
            throw new IllegalArgumentException("Invalid position");
        }
        currentIndex = i;
        return current();
    }
    
    public int getBeginIndex() {
        return rangeStart;
    }
    
    public int getEndIndex() {
        return rangeLimit;
    }
    
    public int getIndex() {
        return currentIndex;
    }
    
    public Object clone() {
        RuleBasedBreakIterator$SafeCharIterator copy = null;
        try {
            copy = (RuleBasedBreakIterator$SafeCharIterator)(RuleBasedBreakIterator$SafeCharIterator)super.clone();
        } catch (CloneNotSupportedException e) {
            throw new Error("Clone not supported: " + e);
        }
        CharacterIterator copyOfBase = (CharacterIterator)(CharacterIterator)base.clone();
        copy.base = copyOfBase;
        return copy;
    }
}
