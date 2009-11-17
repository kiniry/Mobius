package org.w3c.dom.ls;

public interface LSResourceResolver {
    
    public LSInput resolveResource(String type, String namespaceURI, String publicId, String systemId, String baseURI);
}
