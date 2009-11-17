package java.text;

import java.util.ArrayList;

class CharacterIteratorFieldDelegate implements Format$FieldDelegate {
    private ArrayList attributedStrings;
    private int size;
    
    CharacterIteratorFieldDelegate() {
        
        attributedStrings = new ArrayList();
    }
    
    public void formatted(Format$Field attr, Object value, int start, int end, StringBuffer buffer) {
        if (start != end) {
            if (start < size) {
                int index = size;
                int asIndex = attributedStrings.size() - 1;
                while (start < index) {
                    AttributedString as = (AttributedString)(AttributedString)attributedStrings.get(asIndex--);
                    int newIndex = index - as.length();
                    int aStart = Math.max(0, start - newIndex);
                    as.addAttribute(attr, value, aStart, Math.min(end - start, as.length() - aStart) + aStart);
                    index = newIndex;
                }
            }
            if (size < start) {
                attributedStrings.add(new AttributedString(buffer.substring(size, start)));
                size = start;
            }
            if (size < end) {
                int aStart = Math.max(start, size);
                AttributedString string = new AttributedString(buffer.substring(aStart, end));
                string.addAttribute(attr, value);
                attributedStrings.add(string);
                size = end;
            }
        }
    }
    
    public void formatted(int fieldID, Format$Field attr, Object value, int start, int end, StringBuffer buffer) {
        formatted(attr, value, start, end, buffer);
    }
    
    public AttributedCharacterIterator getIterator(String string) {
        if (string.length() > size) {
            attributedStrings.add(new AttributedString(string.substring(size)));
            size = string.length();
        }
        int iCount = attributedStrings.size();
        AttributedCharacterIterator[] iterators = new AttributedCharacterIterator[iCount];
        for (int counter = 0; counter < iCount; counter++) {
            iterators[counter] = ((AttributedString)(AttributedString)attributedStrings.get(counter)).getIterator();
        }
        return new AttributedString(iterators).getIterator();
    }
}
