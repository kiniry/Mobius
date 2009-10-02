package java.util.prefs;

import java.util.*;
import java.io.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;
import org.xml.sax.*;
import org.w3c.dom.*;

class XmlSupport$EH implements ErrorHandler {
    
    /*synthetic*/ XmlSupport$EH(java.util.prefs.XmlSupport$1 x0) {
        this();
    }
    
    private XmlSupport$EH() {
        
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
