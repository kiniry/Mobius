package java.text;

import java.util.*;
import java.text.AttributedCharacterIterator.Attribute;

final class AttributedString$AttributeMap extends AbstractMap {
    /*synthetic*/ final AttributedString this$0;
    int runIndex;
    int beginIndex;
    int endIndex;
    
    AttributedString$AttributeMap(/*synthetic*/ final AttributedString this$0, int runIndex, int beginIndex, int endIndex) {
        this.this$0 = this$0;
        
        this.runIndex = runIndex;
        this.beginIndex = beginIndex;
        this.endIndex = endIndex;
    }
    
    public Set entrySet() {
        HashSet set = new HashSet();
        synchronized (this$0) {
            int size = this$0.runAttributes[runIndex].size();
            for (int i = 0; i < size; i++) {
                AttributedCharacterIterator$Attribute key = (AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)this$0.runAttributes[runIndex].get(i);
                Object value = this$0.runAttributeValues[runIndex].get(i);
                if (value instanceof Annotation) {
                    value = AttributedString.access$400(this$0, key, runIndex, beginIndex, endIndex);
                    if (value == null) {
                        continue;
                    }
                }
                Map$Entry entry = new AttributeEntry(key, value);
                set.add(entry);
            }
        }
        return set;
    }
    
    public Object get(Object key) {
        return AttributedString.access$400(this$0, (AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)key, runIndex, beginIndex, endIndex);
    }
}
