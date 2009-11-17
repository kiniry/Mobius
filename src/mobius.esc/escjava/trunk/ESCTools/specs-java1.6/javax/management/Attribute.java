package javax.management;

import java.io.Serializable;

public class Attribute implements Serializable {
    private static final long serialVersionUID = 2484220110589082382L;
    private String name;
    private Object value = null;
    
    public Attribute(String name, Object value) {
        
        if (name == null) {
            throw new RuntimeOperationsException(new IllegalArgumentException("Attribute name cannot be null "));
        }
        this.name = name;
        this.value = value;
    }
    
    public String getName() {
        return name;
    }
    
    public Object getValue() {
        return value;
    }
    
    public boolean equals(Object object) {
        if (!(object instanceof Attribute)) {
            return false;
        }
        Attribute val = (Attribute)(Attribute)object;
        if (value == null) {
            if (val.getValue() == null) {
                return name.equals(val.getName());
            } else {
                return false;
            }
        }
        return ((name.equals(val.getName())) && (value.equals(val.getValue())));
    }
}
