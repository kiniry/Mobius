package javax.xml.transform;

import java.util.Properties;

public abstract class Transformer {
    
    protected Transformer() {
        
    }
    
    public void reset() {
        throw new UnsupportedOperationException("This Transformer, \"" + this.getClass().getName() + "\", does not support the reset functionality." + "  Specification \"" + this.getClass().getPackage().getSpecificationTitle() + "\"" + " version \"" + this.getClass().getPackage().getSpecificationVersion() + "\"");
    }
    
    public abstract void transform(Source xmlSource, Result outputTarget) throws TransformerException;
    
    public abstract void setParameter(String name, Object value);
    
    public abstract Object getParameter(String name);
    
    public abstract void clearParameters();
    
    public abstract void setURIResolver(URIResolver resolver);
    
    public abstract URIResolver getURIResolver();
    
    public abstract void setOutputProperties(Properties oformat);
    
    public abstract Properties getOutputProperties();
    
    public abstract void setOutputProperty(String name, String value) throws IllegalArgumentException;
    
    public abstract String getOutputProperty(String name) throws IllegalArgumentException;
    
    public abstract void setErrorListener(ErrorListener listener) throws IllegalArgumentException;
    
    public abstract ErrorListener getErrorListener();
}
