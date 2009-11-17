package java.beans;

public interface BeanInfo {
    
    BeanDescriptor getBeanDescriptor();
    
    EventSetDescriptor[] getEventSetDescriptors();
    
    int getDefaultEventIndex();
    
    PropertyDescriptor[] getPropertyDescriptors();
    
    int getDefaultPropertyIndex();
    
    MethodDescriptor[] getMethodDescriptors();
    
    BeanInfo[] getAdditionalBeanInfo();
    
    java.awt.Image getIcon(int iconKind);
    static final int ICON_COLOR_16x16 = 1;
    static final int ICON_COLOR_32x32 = 2;
    static final int ICON_MONO_16x16 = 3;
    static final int ICON_MONO_32x32 = 4;
}
