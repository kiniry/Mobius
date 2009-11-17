package javax.print.attribute;

import java.io.Serializable;

public interface Attribute extends Serializable {
    
    public Class getCategory();
    
    public String getName();
}
