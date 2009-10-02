package javax.management;

public interface MBeanRegistration {
    
    public ObjectName preRegister(MBeanServer server, ObjectName name) throws java.lang.Exception;
    
    public void postRegister(Boolean registrationDone);
    
    public void preDeregister() throws java.lang.Exception;
    
    public void postDeregister();
}
