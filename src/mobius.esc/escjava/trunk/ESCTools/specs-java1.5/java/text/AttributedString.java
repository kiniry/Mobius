package java.text;

import java.util.*;
import java.text.AttributedCharacterIterator.Attribute;

public class AttributedString {
    
    /*synthetic*/ static Object access$400(AttributedString x0, AttributedCharacterIterator$Attribute x1, int x2, int x3, int x4) {
        return x0.getAttributeCheckRange(x1, x2, x3, x4);
    }
    
    /*synthetic*/ static boolean access$300(AttributedString x0, Set x1, int x2, int x3) {
        return x0.attributeValuesMatch(x1, x2, x3);
    }
    
    /*synthetic*/ static boolean access$200(Object x0, Object x1) {
        return valuesMatch(x0, x1);
    }
    
    /*synthetic*/ static Object access$100(AttributedString x0, AttributedCharacterIterator$Attribute x1, int x2) {
        return x0.getAttribute(x1, x2);
    }
    
    /*synthetic*/ static char access$000(AttributedString x0, int x1) {
        return x0.charAt(x1);
    }
    private static final int ARRAY_SIZE_INCREMENT = 10;
    String text;
    int runArraySize;
    int runCount;
    int[] runStarts;
    Vector[] runAttributes;
    Vector[] runAttributeValues;
    
    AttributedString(AttributedCharacterIterator[] iterators) {
        
        if (iterators == null) {
            throw new NullPointerException("Iterators must not be null");
        }
        if (iterators.length == 0) {
            text = "";
        } else {
            StringBuffer buffer = new StringBuffer();
            for (int counter = 0; counter < iterators.length; counter++) {
                appendContents(buffer, iterators[counter]);
            }
            text = buffer.toString();
            if (text.length() > 0) {
                int offset = 0;
                Map last = null;
                for (int counter = 0; counter < iterators.length; counter++) {
                    AttributedCharacterIterator iterator = iterators[counter];
                    int start = iterator.getBeginIndex();
                    int end = iterator.getEndIndex();
                    int index = start;
                    while (index < end) {
                        iterator.setIndex(index);
                        Map attrs = iterator.getAttributes();
                        if (mapsDiffer(last, attrs)) {
                            setAttributes(attrs, index - start + offset);
                        }
                        last = attrs;
                        index = iterator.getRunLimit();
                    }
                    offset += (end - start);
                }
            }
        }
    }
    
    public AttributedString(String text) {
        
        if (text == null) {
            throw new NullPointerException();
        }
        this.text = text;
    }
    
    public AttributedString(String text, Map attributes) {
        
        if (text == null || attributes == null) {
            throw new NullPointerException();
        }
        this.text = text;
        if (text.length() == 0) {
            if (attributes.isEmpty()) return;
            throw new IllegalArgumentException("Can\'t add attribute to 0-length text");
        }
        int attributeCount = attributes.size();
        if (attributeCount > 0) {
            createRunAttributeDataVectors();
            Vector newRunAttributes = new Vector(attributeCount);
            Vector newRunAttributeValues = new Vector(attributeCount);
            runAttributes[0] = newRunAttributes;
            runAttributeValues[0] = newRunAttributeValues;
            Iterator iterator = attributes.entrySet().iterator();
            while (iterator.hasNext()) {
                Map$Entry entry = (Map$Entry)(Map$Entry)iterator.next();
                newRunAttributes.addElement(entry.getKey());
                newRunAttributeValues.addElement(entry.getValue());
            }
        }
    }
    
    public AttributedString(AttributedCharacterIterator text) {
        this(text, text.getBeginIndex(), text.getEndIndex(), null);
    }
    
    public AttributedString(AttributedCharacterIterator text, int beginIndex, int endIndex) {
        this(text, beginIndex, endIndex, null);
    }
    
    public AttributedString(AttributedCharacterIterator text, int beginIndex, int endIndex, AttributedCharacterIterator$Attribute[] attributes) {
        
        if (text == null) {
            throw new NullPointerException();
        }
        int textBeginIndex = text.getBeginIndex();
        int textEndIndex = text.getEndIndex();
        if (beginIndex < textBeginIndex || endIndex > textEndIndex || beginIndex > endIndex) throw new IllegalArgumentException("Invalid substring range");
        StringBuffer textBuffer = new StringBuffer();
        text.setIndex(beginIndex);
        for (char c = text.current(); text.getIndex() < endIndex; c = text.next()) textBuffer.append(c);
        this.text = textBuffer.toString();
        if (beginIndex == endIndex) return;
        HashSet keys = new HashSet();
        if (attributes == null) {
            keys.addAll(text.getAllAttributeKeys());
        } else {
            for (int i = 0; i < attributes.length; i++) keys.add(attributes[i]);
            keys.retainAll(text.getAllAttributeKeys());
        }
        if (keys.isEmpty()) return;
        Iterator itr = keys.iterator();
        while (itr.hasNext()) {
            AttributedCharacterIterator$Attribute attributeKey = (AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)itr.next();
            text.setIndex(textBeginIndex);
            while (text.getIndex() < endIndex) {
                int start = text.getRunStart(attributeKey);
                int limit = text.getRunLimit(attributeKey);
                Object value = text.getAttribute(attributeKey);
                if (value != null) {
                    if (value instanceof Annotation) {
                        if (start >= beginIndex && limit <= endIndex) {
                            addAttribute(attributeKey, value, start - beginIndex, limit - beginIndex);
                        } else {
                            if (limit > endIndex) break;
                        }
                    } else {
                        if (start >= endIndex) break;
                        if (limit > beginIndex) {
                            if (start < beginIndex) start = beginIndex;
                            if (limit > endIndex) limit = endIndex;
                            if (start != limit) {
                                addAttribute(attributeKey, value, start - beginIndex, limit - beginIndex);
                            }
                        }
                    }
                }
                text.setIndex(limit);
            }
        }
    }
    
    public void addAttribute(AttributedCharacterIterator$Attribute attribute, Object value) {
        if (attribute == null) {
            throw new NullPointerException();
        }
        int len = length();
        if (len == 0) {
            throw new IllegalArgumentException("Can\'t add attribute to 0-length text");
        }
        addAttributeImpl(attribute, value, 0, len);
    }
    
    public void addAttribute(AttributedCharacterIterator$Attribute attribute, Object value, int beginIndex, int endIndex) {
        if (attribute == null) {
            throw new NullPointerException();
        }
        if (beginIndex < 0 || endIndex > length() || beginIndex >= endIndex) {
            throw new IllegalArgumentException("Invalid substring range");
        }
        addAttributeImpl(attribute, value, beginIndex, endIndex);
    }
    
    public void addAttributes(Map attributes, int beginIndex, int endIndex) {
        if (attributes == null) {
            throw new NullPointerException();
        }
        if (beginIndex < 0 || endIndex > length() || beginIndex > endIndex) {
            throw new IllegalArgumentException("Invalid substring range");
        }
        if (beginIndex == endIndex) {
            if (attributes.isEmpty()) return;
            throw new IllegalArgumentException("Can\'t add attribute to 0-length text");
        }
        if (runCount == 0) {
            createRunAttributeDataVectors();
        }
        int beginRunIndex = ensureRunBreak(beginIndex);
        int endRunIndex = ensureRunBreak(endIndex);
        Iterator iterator = attributes.entrySet().iterator();
        while (iterator.hasNext()) {
            Map$Entry entry = (Map$Entry)(Map$Entry)iterator.next();
            addAttributeRunData((AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)entry.getKey(), entry.getValue(), beginRunIndex, endRunIndex);
        }
    }
    
    private synchronized void addAttributeImpl(AttributedCharacterIterator$Attribute attribute, Object value, int beginIndex, int endIndex) {
        if (runCount == 0) {
            createRunAttributeDataVectors();
        }
        int beginRunIndex = ensureRunBreak(beginIndex);
        int endRunIndex = ensureRunBreak(endIndex);
        addAttributeRunData(attribute, value, beginRunIndex, endRunIndex);
    }
    
    private final void createRunAttributeDataVectors() {
        int[] newRunStarts = new int[ARRAY_SIZE_INCREMENT];
        Vector[] newRunAttributes = new Vector[ARRAY_SIZE_INCREMENT];
        Vector[] newRunAttributeValues = new Vector[ARRAY_SIZE_INCREMENT];
        runStarts = newRunStarts;
        runAttributes = newRunAttributes;
        runAttributeValues = newRunAttributeValues;
        runArraySize = ARRAY_SIZE_INCREMENT;
        runCount = 1;
    }
    
    private final int ensureRunBreak(int offset) {
        return ensureRunBreak(offset, true);
    }
    
    private final int ensureRunBreak(int offset, boolean copyAttrs) {
        if (offset == length()) {
            return runCount;
        }
        int runIndex = 0;
        while (runIndex < runCount && runStarts[runIndex] < offset) {
            runIndex++;
        }
        if (runIndex < runCount && runStarts[runIndex] == offset) {
            return runIndex;
        }
        if (runCount == runArraySize) {
            int newArraySize = runArraySize + ARRAY_SIZE_INCREMENT;
            int[] newRunStarts = new int[newArraySize];
            Vector[] newRunAttributes = new Vector[newArraySize];
            Vector[] newRunAttributeValues = new Vector[newArraySize];
            for (int i = 0; i < runArraySize; i++) {
                newRunStarts[i] = runStarts[i];
                newRunAttributes[i] = runAttributes[i];
                newRunAttributeValues[i] = runAttributeValues[i];
            }
            runStarts = newRunStarts;
            runAttributes = newRunAttributes;
            runAttributeValues = newRunAttributeValues;
            runArraySize = newArraySize;
        }
        Vector newRunAttributes = null;
        Vector newRunAttributeValues = null;
        if (copyAttrs) {
            Vector oldRunAttributes = runAttributes[runIndex - 1];
            Vector oldRunAttributeValues = runAttributeValues[runIndex - 1];
            if (oldRunAttributes != null) {
                newRunAttributes = (Vector)(Vector)oldRunAttributes.clone();
            }
            if (oldRunAttributeValues != null) {
                newRunAttributeValues = (Vector)(Vector)oldRunAttributeValues.clone();
            }
        }
        runCount++;
        for (int i = runCount - 1; i > runIndex; i--) {
            runStarts[i] = runStarts[i - 1];
            runAttributes[i] = runAttributes[i - 1];
            runAttributeValues[i] = runAttributeValues[i - 1];
        }
        runStarts[runIndex] = offset;
        runAttributes[runIndex] = newRunAttributes;
        runAttributeValues[runIndex] = newRunAttributeValues;
        return runIndex;
    }
    
    private void addAttributeRunData(AttributedCharacterIterator$Attribute attribute, Object value, int beginRunIndex, int endRunIndex) {
        for (int i = beginRunIndex; i < endRunIndex; i++) {
            int keyValueIndex = -1;
            if (runAttributes[i] == null) {
                Vector newRunAttributes = new Vector();
                Vector newRunAttributeValues = new Vector();
                runAttributes[i] = newRunAttributes;
                runAttributeValues[i] = newRunAttributeValues;
            } else {
                keyValueIndex = runAttributes[i].indexOf(attribute);
            }
            if (keyValueIndex == -1) {
                int oldSize = runAttributes[i].size();
                runAttributes[i].addElement(attribute);
                try {
                    runAttributeValues[i].addElement(value);
                } catch (Exception e) {
                    runAttributes[i].setSize(oldSize);
                    runAttributeValues[i].setSize(oldSize);
                }
            } else {
                runAttributeValues[i].set(keyValueIndex, value);
            }
        }
    }
    
    public AttributedCharacterIterator getIterator() {
        return getIterator(null, 0, length());
    }
    
    public AttributedCharacterIterator getIterator(AttributedCharacterIterator$Attribute[] attributes) {
        return getIterator(attributes, 0, length());
    }
    
    public AttributedCharacterIterator getIterator(AttributedCharacterIterator$Attribute[] attributes, int beginIndex, int endIndex) {
        return new AttributedString$AttributedStringIterator(this, attributes, beginIndex, endIndex);
    }
    
    int length() {
        return text.length();
    }
    
    private char charAt(int index) {
        return text.charAt(index);
    }
    
    private synchronized Object getAttribute(AttributedCharacterIterator$Attribute attribute, int runIndex) {
        Vector currentRunAttributes = runAttributes[runIndex];
        Vector currentRunAttributeValues = runAttributeValues[runIndex];
        if (currentRunAttributes == null) {
            return null;
        }
        int attributeIndex = currentRunAttributes.indexOf(attribute);
        if (attributeIndex != -1) {
            return currentRunAttributeValues.elementAt(attributeIndex);
        } else {
            return null;
        }
    }
    
    private Object getAttributeCheckRange(AttributedCharacterIterator$Attribute attribute, int runIndex, int beginIndex, int endIndex) {
        Object value = getAttribute(attribute, runIndex);
        if (value instanceof Annotation) {
            if (beginIndex > 0) {
                int currIndex = runIndex;
                int runStart = runStarts[currIndex];
                while (runStart >= beginIndex && valuesMatch(value, getAttribute(attribute, currIndex - 1))) {
                    currIndex--;
                    runStart = runStarts[currIndex];
                }
                if (runStart < beginIndex) {
                    return null;
                }
            }
            int textLength = length();
            if (endIndex < textLength) {
                int currIndex = runIndex;
                int runLimit = (currIndex < runCount - 1) ? runStarts[currIndex + 1] : textLength;
                while (runLimit <= endIndex && valuesMatch(value, getAttribute(attribute, currIndex + 1))) {
                    currIndex++;
                    runLimit = (currIndex < runCount - 1) ? runStarts[currIndex + 1] : textLength;
                }
                if (runLimit > endIndex) {
                    return null;
                }
            }
        }
        return value;
    }
    
    private boolean attributeValuesMatch(Set attributes, int runIndex1, int runIndex2) {
        Iterator iterator = attributes.iterator();
        while (iterator.hasNext()) {
            AttributedCharacterIterator$Attribute key = (AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)iterator.next();
            if (!valuesMatch(getAttribute(key, runIndex1), getAttribute(key, runIndex2))) {
                return false;
            }
        }
        return true;
    }
    
    private static final boolean valuesMatch(Object value1, Object value2) {
        if (value1 == null) {
            return value2 == null;
        } else {
            return value1.equals(value2);
        }
    }
    
    private final void appendContents(StringBuffer buf, CharacterIterator iterator) {
        int index = iterator.getBeginIndex();
        int end = iterator.getEndIndex();
        while (index < end) {
            iterator.setIndex(index++);
            buf.append(iterator.current());
        }
    }
    
    private void setAttributes(Map attrs, int offset) {
        if (runCount == 0) {
            createRunAttributeDataVectors();
        }
        int index = ensureRunBreak(offset, false);
        int size;
        if (attrs != null && (size = attrs.size()) > 0) {
            Vector runAttrs = new Vector(size);
            Vector runValues = new Vector(size);
            Iterator iterator = attrs.entrySet().iterator();
            while (iterator.hasNext()) {
                Map$Entry entry = (Map$Entry)(Map$Entry)iterator.next();
                runAttrs.add(entry.getKey());
                runValues.add(entry.getValue());
            }
            runAttributes[index] = runAttrs;
            runAttributeValues[index] = runValues;
        }
    }
    
    private static boolean mapsDiffer(Map last, Map attrs) {
        if (last == null) {
            return (attrs != null && attrs.size() > 0);
        }
        return (!last.equals(attrs));
    }
    {
    }
    {
    }
}
