package java.text;

import java.util.Map;
import java.util.Set;

public interface AttributedCharacterIterator extends CharacterIterator {
    
    public int getRunStart();
    
    public int getRunStart(AttributedCharacterIterator$Attribute attribute);
    
    public int getRunStart(Set attributes);
    
    public int getRunLimit();
    
    public int getRunLimit(AttributedCharacterIterator$Attribute attribute);
    
    public int getRunLimit(Set attributes);
    
    public Map getAttributes();
    
    public Object getAttribute(AttributedCharacterIterator$Attribute attribute);
    
    public Set getAllAttributeKeys();
}
