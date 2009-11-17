package java.beans;

class GenericBeanInfo extends SimpleBeanInfo {
    private BeanDescriptor beanDescriptor;
    private EventSetDescriptor[] events;
    private int defaultEvent;
    private PropertyDescriptor[] properties;
    private int defaultProperty;
    private MethodDescriptor[] methods;
    private BeanInfo targetBeanInfo;
    
    public GenericBeanInfo(BeanDescriptor beanDescriptor, EventSetDescriptor[] events, int defaultEvent, PropertyDescriptor[] properties, int defaultProperty, MethodDescriptor[] methods, BeanInfo targetBeanInfo) {
        
        this.beanDescriptor = beanDescriptor;
        this.events = events;
        this.defaultEvent = defaultEvent;
        this.properties = properties;
        this.defaultProperty = defaultProperty;
        this.methods = methods;
        this.targetBeanInfo = targetBeanInfo;
    }
    
    GenericBeanInfo(GenericBeanInfo old) {
        
        beanDescriptor = new BeanDescriptor(old.beanDescriptor);
        if (old.events != null) {
            int len = old.events.length;
            events = new EventSetDescriptor[len];
            for (int i = 0; i < len; i++) {
                events[i] = new EventSetDescriptor(old.events[i]);
            }
        }
        defaultEvent = old.defaultEvent;
        if (old.properties != null) {
            int len = old.properties.length;
            properties = new PropertyDescriptor[len];
            for (int i = 0; i < len; i++) {
                PropertyDescriptor oldp = old.properties[i];
                if (oldp instanceof IndexedPropertyDescriptor) {
                    properties[i] = new IndexedPropertyDescriptor((IndexedPropertyDescriptor)(IndexedPropertyDescriptor)oldp);
                } else {
                    properties[i] = new PropertyDescriptor(oldp);
                }
            }
        }
        defaultProperty = old.defaultProperty;
        if (old.methods != null) {
            int len = old.methods.length;
            methods = new MethodDescriptor[len];
            for (int i = 0; i < len; i++) {
                methods[i] = new MethodDescriptor(old.methods[i]);
            }
        }
        targetBeanInfo = old.targetBeanInfo;
    }
    
    public PropertyDescriptor[] getPropertyDescriptors() {
        return properties;
    }
    
    public int getDefaultPropertyIndex() {
        return defaultProperty;
    }
    
    public EventSetDescriptor[] getEventSetDescriptors() {
        return events;
    }
    
    public int getDefaultEventIndex() {
        return defaultEvent;
    }
    
    public MethodDescriptor[] getMethodDescriptors() {
        return methods;
    }
    
    public BeanDescriptor getBeanDescriptor() {
        return beanDescriptor;
    }
    
    public java.awt.Image getIcon(int iconKind) {
        if (targetBeanInfo != null) {
            return targetBeanInfo.getIcon(iconKind);
        }
        return super.getIcon(iconKind);
    }
}
