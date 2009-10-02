package javax.print.attribute;

public interface DocAttributeSet extends AttributeSet {
    
    public boolean add(Attribute attribute);
    
    public boolean addAll(AttributeSet attributes);
}
