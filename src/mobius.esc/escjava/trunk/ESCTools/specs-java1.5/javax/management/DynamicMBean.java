package javax.management;

public interface DynamicMBean {
    
    public Object getAttribute(String attribute) throws AttributeNotFoundException, MBeanException, ReflectionException;
    
    public void setAttribute(Attribute attribute) throws AttributeNotFoundException, InvalidAttributeValueException, MBeanException, ReflectionException;
    
    public AttributeList getAttributes(String[] attributes);
    
    public AttributeList setAttributes(AttributeList attributes);
    
    public Object invoke(String actionName, Object[] params, String[] signature) throws MBeanException, ReflectionException;
    
    public MBeanInfo getMBeanInfo();
}
