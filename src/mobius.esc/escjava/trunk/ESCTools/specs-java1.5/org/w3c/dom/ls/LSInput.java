package org.w3c.dom.ls;

public interface LSInput {
    
    public java.io.Reader getCharacterStream();
    
    public void setCharacterStream(java.io.Reader characterStream);
    
    public java.io.InputStream getByteStream();
    
    public void setByteStream(java.io.InputStream byteStream);
    
    public String getStringData();
    
    public void setStringData(String stringData);
    
    public String getSystemId();
    
    public void setSystemId(String systemId);
    
    public String getPublicId();
    
    public void setPublicId(String publicId);
    
    public String getBaseURI();
    
    public void setBaseURI(String baseURI);
    
    public String getEncoding();
    
    public void setEncoding(String encoding);
    
    public boolean getCertifiedText();
    
    public void setCertifiedText(boolean certifiedText);
}
