package java.text;

import java.util.Vector;
import java.util.Stack;
import java.text.CharacterIterator;
import java.io.IOException;

class DictionaryBasedBreakIterator extends RuleBasedBreakIterator {
    private BreakDictionary dictionary;
    private boolean[] categoryFlags;
    private int dictionaryCharCount;
    private int[] cachedBreakPositions;
    private int positionInCache;
    
    public DictionaryBasedBreakIterator(String dataFile, String dictionaryFile) throws IOException {
        super(dataFile);
        byte[] tmp = super.getAdditionalData();
        if (tmp != null) {
            prepareCategoryFlags(tmp);
            super.setAdditionalData(null);
        }
        dictionary = new BreakDictionary(dictionaryFile);
    }
    
    private void prepareCategoryFlags(byte[] data) {
        categoryFlags = new boolean[data.length];
        for (int i = 0; i < data.length; i++) {
            categoryFlags[i] = (data[i] == (byte)1) ? true : false;
        }
    }
    
    public void setText(CharacterIterator newText) {
        super.setText(newText);
        cachedBreakPositions = null;
        dictionaryCharCount = 0;
        positionInCache = 0;
    }
    
    public int first() {
        cachedBreakPositions = null;
        dictionaryCharCount = 0;
        positionInCache = 0;
        return super.first();
    }
    
    public int last() {
        cachedBreakPositions = null;
        dictionaryCharCount = 0;
        positionInCache = 0;
        return super.last();
    }
    
    public int previous() {
        CharacterIterator text = getText();
        if (cachedBreakPositions != null && positionInCache > 0) {
            --positionInCache;
            text.setIndex(cachedBreakPositions[positionInCache]);
            return cachedBreakPositions[positionInCache];
        } else {
            cachedBreakPositions = null;
            int result = super.previous();
            if (cachedBreakPositions != null) {
                positionInCache = cachedBreakPositions.length - 2;
            }
            return result;
        }
    }
    
    public int preceding(int offset) {
        CharacterIterator text = getText();
        checkOffset(offset, text);
        if (cachedBreakPositions == null || offset <= cachedBreakPositions[0] || offset > cachedBreakPositions[cachedBreakPositions.length - 1]) {
            cachedBreakPositions = null;
            return super.preceding(offset);
        } else {
            positionInCache = 0;
            while (positionInCache < cachedBreakPositions.length && offset > cachedBreakPositions[positionInCache]) {
                ++positionInCache;
            }
            --positionInCache;
            text.setIndex(cachedBreakPositions[positionInCache]);
            return text.getIndex();
        }
    }
    
    public int following(int offset) {
        CharacterIterator text = getText();
        checkOffset(offset, text);
        if (cachedBreakPositions == null || offset < cachedBreakPositions[0] || offset >= cachedBreakPositions[cachedBreakPositions.length - 1]) {
            cachedBreakPositions = null;
            return super.following(offset);
        } else {
            positionInCache = 0;
            while (positionInCache < cachedBreakPositions.length && offset >= cachedBreakPositions[positionInCache]) {
                ++positionInCache;
            }
            text.setIndex(cachedBreakPositions[positionInCache]);
            return text.getIndex();
        }
    }
    
    protected int handleNext() {
        CharacterIterator text = getText();
        if (cachedBreakPositions == null || positionInCache == cachedBreakPositions.length - 1) {
            int startPos = text.getIndex();
            dictionaryCharCount = 0;
            int result = super.handleNext();
            if (dictionaryCharCount > 1 && result - startPos > 1) {
                divideUpDictionaryRange(startPos, result);
            } else {
                cachedBreakPositions = null;
                return result;
            }
        }
        if (cachedBreakPositions != null) {
            ++positionInCache;
            text.setIndex(cachedBreakPositions[positionInCache]);
            return cachedBreakPositions[positionInCache];
        }
        return -9999;
    }
    
    protected int lookupCategory(int c) {
        int result = super.lookupCategory(c);
        if (result != RuleBasedBreakIterator.IGNORE && categoryFlags[result]) {
            ++dictionaryCharCount;
        }
        return result;
    }
    
    private void divideUpDictionaryRange(int startPos, int endPos) {
        CharacterIterator text = getText();
        text.setIndex(startPos);
        int c = getCurrent();
        int category = lookupCategory(c);
        while (category == IGNORE || !categoryFlags[category]) {
            c = getNext();
            category = lookupCategory(c);
        }
        Stack currentBreakPositions = new Stack();
        Stack possibleBreakPositions = new Stack();
        Vector wrongBreakPositions = new Vector();
        int state = 0;
        int farthestEndPoint = text.getIndex();
        Stack bestBreakPositions = null;
        c = getCurrent();
        while (true) {
            if (dictionary.getNextState(state, 0) == -1) {
                possibleBreakPositions.push(new Integer(text.getIndex()));
            }
            state = dictionary.getNextStateFromCharacter(state, c);
            if (state == -1) {
                currentBreakPositions.push(new Integer(text.getIndex()));
                break;
            } else if (state == 0 || text.getIndex() >= endPos) {
                if (text.getIndex() > farthestEndPoint) {
                    farthestEndPoint = text.getIndex();
                    bestBreakPositions = (Stack)((Stack)currentBreakPositions.clone());
                }
                Integer newStartingSpot = null;
                while (!possibleBreakPositions.isEmpty() && wrongBreakPositions.contains(possibleBreakPositions.peek())) {
                    possibleBreakPositions.pop();
                }
                if (possibleBreakPositions.isEmpty()) {
                    if (bestBreakPositions != null) {
                        currentBreakPositions = bestBreakPositions;
                        if (farthestEndPoint < endPos) {
                            text.setIndex(farthestEndPoint + 1);
                        } else {
                            break;
                        }
                    } else {
                        if ((currentBreakPositions.size() == 0 || ((Integer)((Integer)currentBreakPositions.peek())).intValue() != text.getIndex()) && text.getIndex() != startPos) {
                            currentBreakPositions.push(new Integer(text.getIndex()));
                        }
                        getNext();
                        currentBreakPositions.push(new Integer(text.getIndex()));
                    }
                } else {
                    Integer temp = (Integer)(Integer)possibleBreakPositions.pop();
                    Object temp2 = null;
                    while (!currentBreakPositions.isEmpty() && temp.intValue() < ((Integer)(Integer)currentBreakPositions.peek()).intValue()) {
                        temp2 = currentBreakPositions.pop();
                        wrongBreakPositions.addElement(temp2);
                    }
                    currentBreakPositions.push(temp);
                    text.setIndex(((Integer)(Integer)currentBreakPositions.peek()).intValue());
                }
                c = getCurrent();
                if (text.getIndex() >= endPos) {
                    break;
                }
            } else {
                c = getNext();
            }
        }
        if (!currentBreakPositions.isEmpty()) {
            currentBreakPositions.pop();
        }
        currentBreakPositions.push(new Integer(endPos));
        cachedBreakPositions = new int[currentBreakPositions.size() + 1];
        cachedBreakPositions[0] = startPos;
        for (int i = 0; i < currentBreakPositions.size(); i++) {
            cachedBreakPositions[i + 1] = ((Integer)(Integer)currentBreakPositions.elementAt(i)).intValue();
        }
        positionInCache = 0;
    }
}
