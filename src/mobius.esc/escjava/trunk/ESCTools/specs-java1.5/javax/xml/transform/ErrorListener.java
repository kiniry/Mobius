package javax.xml.transform;

public interface ErrorListener {
    
    public abstract void warning(TransformerException exception) throws TransformerException;
    
    public abstract void error(TransformerException exception) throws TransformerException;
    
    public abstract void fatalError(TransformerException exception) throws TransformerException;
}
