package java.beans;

public class SimpleBeanInfo implements BeanInfo {
    
    public SimpleBeanInfo() {
        
    }
    
    public BeanDescriptor getBeanDescriptor() {
        return null;
    }
    
    public PropertyDescriptor[] getPropertyDescriptors() {
        return null;
    }
    
    public int getDefaultPropertyIndex() {
        return -1;
    }
    
    public EventSetDescriptor[] getEventSetDescriptors() {
        return null;
    }
    
    public int getDefaultEventIndex() {
        return -1;
    }
    
    public MethodDescriptor[] getMethodDescriptors() {
        return null;
    }
    
    public BeanInfo[] getAdditionalBeanInfo() {
        return null;
    }
    
    public java.awt.Image getIcon(int iconKind) {
        return null;
    }
    
    public java.awt.Image loadImage(final String resourceName) {
        try {
            final Class c = getClass();
            java.awt.image.ImageProducer ip = (java.awt.image.ImageProducer)(java.awt.image.ImageProducer)java.security.AccessController.doPrivileged(new SimpleBeanInfo$1(this, c, resourceName));
            if (ip == null) return null;
            java.awt.Toolkit tk = java.awt.Toolkit.getDefaultToolkit();
            return tk.createImage(ip);
        } catch (Exception ex) {
            return null;
        }
    }
}
