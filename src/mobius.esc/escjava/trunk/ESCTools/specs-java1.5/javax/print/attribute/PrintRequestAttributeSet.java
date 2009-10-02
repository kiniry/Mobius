package javax.print.attribute;

public interface PrintRequestAttributeSet extends AttributeSet {
    
    public boolean add(Attribute attribute);
    
    public boolean addAll(AttributeSet attributes);
}
