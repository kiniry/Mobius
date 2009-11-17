package javax.swing.text;

public interface Element {
    
    public Document getDocument();
    
    public Element getParentElement();
    
    public String getName();
    
    public AttributeSet getAttributes();
    
    public int getStartOffset();
    
    public int getEndOffset();
    
    public int getElementIndex(int offset);
    
    public int getElementCount();
    
    public Element getElement(int index);
    
    public boolean isLeaf();
}
