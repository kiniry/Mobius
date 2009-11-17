package java.text;

import java.util.*;
import java.text.AttributedCharacterIterator.Attribute;

class AttributeEntry implements Map$Entry {
    private AttributedCharacterIterator$Attribute key;
    private Object value;
    
    AttributeEntry(AttributedCharacterIterator$Attribute key, Object value) {
        
        this.key = key;
        this.value = value;
    }
    
    public boolean equals(Object o) {
        if (!(o instanceof AttributeEntry)) {
            return false;
        }
        AttributeEntry other = (AttributeEntry)(AttributeEntry)o;
        return other.key.equals(key) && (value == null ? other.value == null : other.value.equals(value));
    }
    
    public Object getKey() {
        return key;
    }
    
    public Object getValue() {
        return value;
    }
    
    public Object setValue(Object newValue) {
        throw new UnsupportedOperationException();
    }
    
    public int hashCode() {
        return key.hashCode() ^ (value == null ? 0 : value.hashCode());
    }
    
    public String toString() {
        return key.toString() + "=" + value.toString();
    }
}
