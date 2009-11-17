package javax.print.attribute;

public interface PrintServiceAttributeSet extends AttributeSet {
    
    public boolean add(Attribute attribute);
    
    public boolean addAll(AttributeSet attributes);
}
