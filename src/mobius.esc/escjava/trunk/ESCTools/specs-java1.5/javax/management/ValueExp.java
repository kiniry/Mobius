package javax.management;

public interface ValueExp extends java.io.Serializable {
    
    public ValueExp apply(ObjectName name) throws BadStringOperationException, BadBinaryOpValueExpException, BadAttributeValueExpException, InvalidApplicationException;
    
    
    public void setMBeanServer(MBeanServer s);
}
