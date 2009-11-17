package java.beans;

import java.lang.ref.Reference;

public class BeanDescriptor extends FeatureDescriptor {
    private Reference beanClassRef;
    private Reference customizerClassRef;
    
    public BeanDescriptor(Class beanClass) {
        this(beanClass, null);
    }
    
    public BeanDescriptor(Class beanClass, Class customizerClass) {
        
        beanClassRef = createReference(beanClass);
        customizerClassRef = createReference(customizerClass);
        String name = beanClass.getName();
        while (name.indexOf('.') >= 0) {
            name = name.substring(name.indexOf('.') + 1);
        }
        setName(name);
    }
    
    public Class getBeanClass() {
        return (Class)(Class)getObject(beanClassRef);
    }
    
    public Class getCustomizerClass() {
        return (Class)(Class)getObject(customizerClassRef);
    }
    
    BeanDescriptor(BeanDescriptor old) {
        super(old);
        beanClassRef = old.beanClassRef;
        customizerClassRef = old.customizerClassRef;
    }
}
