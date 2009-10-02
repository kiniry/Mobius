package javax.management;

import java.io.Serializable;

public interface QueryExp extends Serializable {
    
    public boolean apply(ObjectName name) throws BadStringOperationException, BadBinaryOpValueExpException, BadAttributeValueExpException, InvalidApplicationException;
    
    public void setMBeanServer(MBeanServer s);
}
