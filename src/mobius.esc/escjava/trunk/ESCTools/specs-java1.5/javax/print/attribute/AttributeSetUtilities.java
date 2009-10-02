package javax.print.attribute;

public final class AttributeSetUtilities {
    
    private AttributeSetUtilities() {
        
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public static AttributeSet unmodifiableView(AttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$UnmodifiableAttributeSet(attributeSet);
    }
    
    public static DocAttributeSet unmodifiableView(DocAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$UnmodifiableDocAttributeSet(attributeSet);
    }
    
    public static PrintRequestAttributeSet unmodifiableView(PrintRequestAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$UnmodifiablePrintRequestAttributeSet(attributeSet);
    }
    
    public static PrintJobAttributeSet unmodifiableView(PrintJobAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$UnmodifiablePrintJobAttributeSet(attributeSet);
    }
    
    public static PrintServiceAttributeSet unmodifiableView(PrintServiceAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$UnmodifiablePrintServiceAttributeSet(attributeSet);
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    
    public static AttributeSet synchronizedView(AttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$SynchronizedAttributeSet(attributeSet);
    }
    
    public static DocAttributeSet synchronizedView(DocAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$SynchronizedDocAttributeSet(attributeSet);
    }
    
    public static PrintRequestAttributeSet synchronizedView(PrintRequestAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$SynchronizedPrintRequestAttributeSet(attributeSet);
    }
    
    public static PrintJobAttributeSet synchronizedView(PrintJobAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$SynchronizedPrintJobAttributeSet(attributeSet);
    }
    
    public static PrintServiceAttributeSet synchronizedView(PrintServiceAttributeSet attributeSet) {
        if (attributeSet == null) {
            throw new NullPointerException();
        }
        return new AttributeSetUtilities$SynchronizedPrintServiceAttributeSet(attributeSet);
    }
    
    public static Class verifyAttributeCategory(Object object, Class interfaceName) {
        Class result = (Class)(Class)object;
        if (interfaceName.isAssignableFrom(result)) {
            return result;
        } else {
            throw new ClassCastException();
        }
    }
    
    public static Attribute verifyAttributeValue(Object object, Class interfaceName) {
        if (object == null) {
            throw new NullPointerException();
        } else if (interfaceName.isInstance(object)) {
            return (Attribute)(Attribute)object;
        } else {
            throw new ClassCastException();
        }
    }
    
    public static void verifyCategoryForValue(Class category, Attribute attribute) {
        if (!category.equals(attribute.getCategory())) {
            throw new IllegalArgumentException();
        }
    }
}
