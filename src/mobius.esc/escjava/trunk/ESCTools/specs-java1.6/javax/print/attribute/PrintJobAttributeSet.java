package javax.print.attribute;

public interface PrintJobAttributeSet extends AttributeSet {
    
    public boolean add(Attribute attribute);
    
    public boolean addAll(AttributeSet attributes);
}
