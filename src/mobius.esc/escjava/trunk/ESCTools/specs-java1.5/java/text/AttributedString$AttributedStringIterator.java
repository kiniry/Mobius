package java.text;

import java.util.*;
import java.text.AttributedCharacterIterator.Attribute;

final class AttributedString$AttributedStringIterator implements AttributedCharacterIterator {
    /*synthetic*/ final AttributedString this$0;
    private int beginIndex;
    private int endIndex;
    private AttributedCharacterIterator$Attribute[] relevantAttributes;
    private int currentIndex;
    private int currentRunIndex;
    private int currentRunStart;
    private int currentRunLimit;
    
    AttributedString$AttributedStringIterator(/*synthetic*/ final AttributedString this$0, AttributedCharacterIterator$Attribute[] attributes, int beginIndex, int endIndex) {
        this.this$0 = this$0;
        
        if (beginIndex < 0 || beginIndex > endIndex || endIndex > this$0.length()) {
            throw new IllegalArgumentException("Invalid substring range");
        }
        this.beginIndex = beginIndex;
        this.endIndex = endIndex;
        this.currentIndex = beginIndex;
        updateRunInfo();
        if (attributes != null) {
            relevantAttributes = (AttributedCharacterIterator$Attribute[])(AttributedCharacterIterator$Attribute[])attributes.clone();
        }
    }
    
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (!(obj instanceof AttributedString$AttributedStringIterator)) {
            return false;
        }
        AttributedString$AttributedStringIterator that = (AttributedString$AttributedStringIterator)(AttributedString$AttributedStringIterator)obj;
        if (this$0 != that.getString()) return false;
        if (currentIndex != that.currentIndex || beginIndex != that.beginIndex || endIndex != that.endIndex) return false;
        return true;
    }
    
    public int hashCode() {
        return this$0.text.hashCode() ^ currentIndex ^ beginIndex ^ endIndex;
    }
    
    public Object clone() {
        try {
            AttributedString$AttributedStringIterator other = (AttributedString$AttributedStringIterator)(AttributedString$AttributedStringIterator)super.clone();
            return other;
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    public char first() {
        return internalSetIndex(beginIndex);
    }
    
    public char last() {
        if (endIndex == beginIndex) {
            return internalSetIndex(endIndex);
        } else {
            return internalSetIndex(endIndex - 1);
        }
    }
    
    public char current() {
        if (currentIndex == endIndex) {
            return DONE;
        } else {
            return AttributedString.access$000(this$0, currentIndex);
        }
    }
    
    public char next() {
        if (currentIndex < endIndex) {
            return internalSetIndex(currentIndex + 1);
        } else {
            return DONE;
        }
    }
    
    public char previous() {
        if (currentIndex > beginIndex) {
            return internalSetIndex(currentIndex - 1);
        } else {
            return DONE;
        }
    }
    
    public char setIndex(int position) {
        if (position < beginIndex || position > endIndex) throw new IllegalArgumentException("Invalid index");
        return internalSetIndex(position);
    }
    
    public int getBeginIndex() {
        return beginIndex;
    }
    
    public int getEndIndex() {
        return endIndex;
    }
    
    public int getIndex() {
        return currentIndex;
    }
    
    public int getRunStart() {
        return currentRunStart;
    }
    
    public int getRunStart(AttributedCharacterIterator$Attribute attribute) {
        if (currentRunStart == beginIndex || currentRunIndex == -1) {
            return currentRunStart;
        } else {
            Object value = getAttribute(attribute);
            int runStart = currentRunStart;
            int runIndex = currentRunIndex;
            while (runStart > beginIndex && AttributedString.access$200(value, AttributedString.access$100(this$0, attribute, runIndex - 1))) {
                runIndex--;
                runStart = this$0.runStarts[runIndex];
            }
            if (runStart < beginIndex) {
                runStart = beginIndex;
            }
            return runStart;
        }
    }
    
    public int getRunStart(Set attributes) {
        if (currentRunStart == beginIndex || currentRunIndex == -1) {
            return currentRunStart;
        } else {
            int runStart = currentRunStart;
            int runIndex = currentRunIndex;
            while (runStart > beginIndex && AttributedString.access$300(this$0, attributes, currentRunIndex, runIndex - 1)) {
                runIndex--;
                runStart = this$0.runStarts[runIndex];
            }
            if (runStart < beginIndex) {
                runStart = beginIndex;
            }
            return runStart;
        }
    }
    
    public int getRunLimit() {
        return currentRunLimit;
    }
    
    public int getRunLimit(AttributedCharacterIterator$Attribute attribute) {
        if (currentRunLimit == endIndex || currentRunIndex == -1) {
            return currentRunLimit;
        } else {
            Object value = getAttribute(attribute);
            int runLimit = currentRunLimit;
            int runIndex = currentRunIndex;
            while (runLimit < endIndex && AttributedString.access$200(value, AttributedString.access$100(this$0, attribute, runIndex + 1))) {
                runIndex++;
                runLimit = runIndex < this$0.runCount - 1 ? this$0.runStarts[runIndex + 1] : endIndex;
            }
            if (runLimit > endIndex) {
                runLimit = endIndex;
            }
            return runLimit;
        }
    }
    
    public int getRunLimit(Set attributes) {
        if (currentRunLimit == endIndex || currentRunIndex == -1) {
            return currentRunLimit;
        } else {
            int runLimit = currentRunLimit;
            int runIndex = currentRunIndex;
            while (runLimit < endIndex && AttributedString.access$300(this$0, attributes, currentRunIndex, runIndex + 1)) {
                runIndex++;
                runLimit = runIndex < this$0.runCount - 1 ? this$0.runStarts[runIndex + 1] : endIndex;
            }
            if (runLimit > endIndex) {
                runLimit = endIndex;
            }
            return runLimit;
        }
    }
    
    public Map getAttributes() {
        if (this$0.runAttributes == null || currentRunIndex == -1 || this$0.runAttributes[currentRunIndex] == null) {
            return new Hashtable();
        }
        return new AttributedString$AttributeMap(this$0, currentRunIndex, beginIndex, endIndex);
    }
    
    public Set getAllAttributeKeys() {
        if (this$0.runAttributes == null) {
            return new HashSet();
        }
        synchronized (this$0) {
            Set keys = new HashSet();
            int i = 0;
            while (i < this$0.runCount) {
                if (this$0.runStarts[i] < endIndex && (i == this$0.runCount - 1 || this$0.runStarts[i + 1] > beginIndex)) {
                    Vector currentRunAttributes = this$0.runAttributes[i];
                    if (currentRunAttributes != null) {
                        int j = currentRunAttributes.size();
                        while (j-- > 0) {
                            keys.add(currentRunAttributes.get(j));
                        }
                    }
                }
                i++;
            }
            return keys;
        }
    }
    
    public Object getAttribute(AttributedCharacterIterator$Attribute attribute) {
        int runIndex = currentRunIndex;
        if (runIndex < 0) {
            return null;
        }
        return AttributedString.access$400(this$0, attribute, runIndex, beginIndex, endIndex);
    }
    
    private AttributedString getString() {
        return this$0;
    }
    
    private char internalSetIndex(int position) {
        currentIndex = position;
        if (position < currentRunStart || position >= currentRunLimit) {
            updateRunInfo();
        }
        if (currentIndex == endIndex) {
            return DONE;
        } else {
            return AttributedString.access$000(this$0, position);
        }
    }
    
    private void updateRunInfo() {
        if (currentIndex == endIndex) {
            currentRunStart = currentRunLimit = endIndex;
            currentRunIndex = -1;
        } else {
            synchronized (this$0) {
                int runIndex = -1;
                while (runIndex < this$0.runCount - 1 && this$0.runStarts[runIndex + 1] <= currentIndex) runIndex++;
                currentRunIndex = runIndex;
                if (runIndex >= 0) {
                    currentRunStart = this$0.runStarts[runIndex];
                    if (currentRunStart < beginIndex) currentRunStart = beginIndex;
                } else {
                    currentRunStart = beginIndex;
                }
                if (runIndex < this$0.runCount - 1) {
                    currentRunLimit = this$0.runStarts[runIndex + 1];
                    if (currentRunLimit > endIndex) currentRunLimit = endIndex;
                } else {
                    currentRunLimit = endIndex;
                }
            }
        }
    }
}
