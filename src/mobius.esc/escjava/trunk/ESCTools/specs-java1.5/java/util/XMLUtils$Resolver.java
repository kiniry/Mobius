package java.util;

import java.io.*;
import org.xml.sax.*;
import org.xml.sax.helpers.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

class XMLUtils$Resolver implements EntityResolver {
    
    /*synthetic*/ XMLUtils$Resolver(java.util.XMLUtils$1 x0) {
        this();
    }
    
    private XMLUtils$Resolver() {
        
    }
    
    public InputSource resolveEntity(String pid, String sid) throws SAXException {
        if (sid.equals("http://java.sun.com/dtd/properties.dtd")) {
            InputSource is;
            is = new InputSource(new StringReader("<?xml version=\"1.0\" encoding=\"UTF-8\"?><!-- DTD for properties --><!ELEMENT properties ( comment?, entry* ) ><!ATTLIST properties version CDATA #FIXED \"1.0\"><!ELEMENT comment (#PCDATA) ><!ELEMENT entry (#PCDATA) ><!ATTLIST entry  key CDATA #REQUIRED>"));
            is.setSystemId("http://java.sun.com/dtd/properties.dtd");
            return is;
        }
        throw new SAXException("Invalid system identifier: " + sid);
    }
}
