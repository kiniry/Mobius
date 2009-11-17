package java.text;

import java.io.InvalidObjectException;
import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

public class AttributedCharacterIterator$Attribute implements Serializable {
    private String name;
    private static final Map instanceMap = new HashMap(7);
    
    protected AttributedCharacterIterator$Attribute(String name) {
        
        this.name = name;
        if (this.getClass() == AttributedCharacterIterator.Attribute.class) {
            instanceMap.put(name, this);
        }
    }
    
    public final boolean equals(Object obj) {
        return super.equals(obj);
    }
    
    public final int hashCode() {
        return super.hashCode();
    }
    
    public String toString() {
        return getClass().getName() + "(" + name + ")";
    }
    
    protected String getName() {
        return name;
    }
    
    protected Object readResolve() throws InvalidObjectException {
        if (this.getClass() != AttributedCharacterIterator.Attribute.class) {
            throw new InvalidObjectException("subclass didn\'t correctly implement readResolve");
        }
        AttributedCharacterIterator$Attribute instance = (AttributedCharacterIterator$Attribute)(AttributedCharacterIterator$Attribute)instanceMap.get(getName());
        if (instance != null) {
            return instance;
        } else {
            throw new InvalidObjectException("unknown attribute name");
        }
    }
    public static final AttributedCharacterIterator$Attribute LANGUAGE = new AttributedCharacterIterator$Attribute("language");
    public static final AttributedCharacterIterator$Attribute READING = new AttributedCharacterIterator$Attribute("reading");
    public static final AttributedCharacterIterator$Attribute INPUT_METHOD_SEGMENT = new AttributedCharacterIterator$Attribute("input_method_segment");
    private static final long serialVersionUID = -9142742483513960612L;
}
