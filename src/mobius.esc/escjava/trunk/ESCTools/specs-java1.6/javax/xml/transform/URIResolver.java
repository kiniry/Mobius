package javax.xml.transform;

public interface URIResolver {
    
    public Source resolve(String href, String base) throws TransformerException;
}
