package java.util.prefs;

import java.util.*;
import java.io.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;
import org.xml.sax.*;
import org.w3c.dom.*;

class XmlSupport$Resolver implements EntityResolver {
    
    /*synthetic*/ XmlSupport$Resolver(java.util.prefs.XmlSupport$1 x0) {
        this();
    }
    
    private XmlSupport$Resolver() {
        
    }
    
    public InputSource resolveEntity(String pid, String sid) throws SAXException {
        if (sid.equals("http://java.sun.com/dtd/preferences.dtd")) {
            InputSource is;
            is = new InputSource(new StringReader("<?xml version=\"1.0\" encoding=\"UTF-8\"?><!-- DTD for preferences --><!ELEMENT preferences (root) ><!ATTLIST preferences EXTERNAL_XML_VERSION CDATA \"0.0\"  ><!ELEMENT root (map, node*) ><!ATTLIST root          type (system|user) #REQUIRED ><!ELEMENT node (map, node*) ><!ATTLIST node          name CDATA #REQUIRED ><!ELEMENT map (entry*) ><!ATTLIST map  MAP_XML_VERSION CDATA \"0.0\"  ><!ELEMENT entry EMPTY ><!ATTLIST entry          key CDATA #REQUIRED          value CDATA #REQUIRED >"));
            is.setSystemId("http://java.sun.com/dtd/preferences.dtd");
            return is;
        }
        throw new SAXException("Invalid system identifier: " + sid);
    }
}
