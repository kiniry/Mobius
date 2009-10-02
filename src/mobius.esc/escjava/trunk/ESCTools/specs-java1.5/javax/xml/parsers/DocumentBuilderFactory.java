package javax.xml.parsers;

import javax.xml.validation.Schema;

public abstract class DocumentBuilderFactory {
    private static final String DEFAULT_PROPERTY_NAME = "javax.xml.parsers.DocumentBuilderFactory";
    private boolean validating = false;
    private boolean namespaceAware = false;
    private boolean whitespace = false;
    private boolean expandEntityRef = true;
    private boolean ignoreComments = false;
    private boolean coalescing = false;
    private boolean canonicalState = false;
    
    protected DocumentBuilderFactory() {
        
    }
    
    public static DocumentBuilderFactory newInstance() {
        try {
            return (DocumentBuilderFactory)(DocumentBuilderFactory)FactoryFinder.find("javax.xml.parsers.DocumentBuilderFactory", "com.sun.org.apache.xerces.internal.jaxp.DocumentBuilderFactoryImpl");
        } catch (FactoryFinder$ConfigurationError e) {
            throw new FactoryConfigurationError(e.getException(), e.getMessage());
        }
    }
    
    public abstract DocumentBuilder newDocumentBuilder() throws ParserConfigurationException;
    
    public void setNamespaceAware(boolean awareness) {
        this.namespaceAware = awareness;
    }
    
    public void setValidating(boolean validating) {
        this.validating = validating;
    }
    
    public void setIgnoringElementContentWhitespace(boolean whitespace) {
        this.whitespace = whitespace;
    }
    
    public void setExpandEntityReferences(boolean expandEntityRef) {
        this.expandEntityRef = expandEntityRef;
    }
    
    public void setIgnoringComments(boolean ignoreComments) {
        this.ignoreComments = ignoreComments;
    }
    
    public void setCoalescing(boolean coalescing) {
        this.coalescing = coalescing;
    }
    
    public boolean isNamespaceAware() {
        return namespaceAware;
    }
    
    public boolean isValidating() {
        return validating;
    }
    
    public boolean isIgnoringElementContentWhitespace() {
        return whitespace;
    }
    
    public boolean isExpandEntityReferences() {
        return expandEntityRef;
    }
    
    public boolean isIgnoringComments() {
        return ignoreComments;
    }
    
    public boolean isCoalescing() {
        return coalescing;
    }
    
    public abstract void setAttribute(String name, Object value) throws IllegalArgumentException;
    
    public abstract Object getAttribute(String name) throws IllegalArgumentException;
    
    public abstract void setFeature(String name, boolean value) throws ParserConfigurationException;
    
    public abstract boolean getFeature(String name) throws ParserConfigurationException;
    
    public Schema getSchema() {
        throw new UnsupportedOperationException("This parser does not support specification \"" + this.getClass().getPackage().getSpecificationTitle() + "\" version \"" + this.getClass().getPackage().getSpecificationVersion() + "\"");
    }
    
    public void setSchema(Schema schema) {
        throw new UnsupportedOperationException("This parser does not support specification \"" + this.getClass().getPackage().getSpecificationTitle() + "\" version \"" + this.getClass().getPackage().getSpecificationVersion() + "\"");
    }
    
    public void setXIncludeAware(final boolean state) {
        throw new UnsupportedOperationException("This parser does not support specification \"" + this.getClass().getPackage().getSpecificationTitle() + "\" version \"" + this.getClass().getPackage().getSpecificationVersion() + "\"");
    }
    
    public boolean isXIncludeAware() {
        throw new UnsupportedOperationException("This parser does not support specification \"" + this.getClass().getPackage().getSpecificationTitle() + "\" version \"" + this.getClass().getPackage().getSpecificationVersion() + "\"");
    }
}
