package java.util;

import java.io.*;
import org.xml.sax.*;
import org.xml.sax.helpers.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

class XMLUtils$EH implements ErrorHandler {
    
    /*synthetic*/ XMLUtils$EH(java.util.XMLUtils$1 x0) {
        this();
    }
    
    private XMLUtils$EH() {
        
    }
    
    public void error(SAXParseException x) throws SAXException {
        throw x;
    }
    
    public void fatalError(SAXParseException x) throws SAXException {
        throw x;
    }
    
    public void warning(SAXParseException x) throws SAXException {
        throw x;
    }
}
