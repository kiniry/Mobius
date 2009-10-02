package java.util;

import java.io.*;
import org.xml.sax.*;
import org.xml.sax.helpers.*;
import org.w3c.dom.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;

class XMLUtils {
    /*synthetic*/ static final boolean $assertionsDisabled = !XMLUtils.class.desiredAssertionStatus();
    {
    }
    
    XMLUtils() {
        
    }
    private static final String PROPS_DTD_URI = "http://java.sun.com/dtd/properties.dtd";
    private static final String PROPS_DTD = "<?xml version=\"1.0\" encoding=\"UTF-8\"?><!-- DTD for properties --><!ELEMENT properties ( comment?, entry* ) ><!ATTLIST properties version CDATA #FIXED \"1.0\"><!ELEMENT comment (#PCDATA) ><!ELEMENT entry (#PCDATA) ><!ATTLIST entry  key CDATA #REQUIRED>";
    private static final String EXTERNAL_XML_VERSION = "1.0";
    
    static void load(Properties props, InputStream in) throws IOException, InvalidPropertiesFormatException {
        Document doc = null;
        try {
            doc = getLoadingDoc(in);
        } catch (SAXException saxe) {
            throw new InvalidPropertiesFormatException(saxe);
        }
        Element propertiesElement = (Element)(Element)doc.getChildNodes().item(1);
        String xmlVersion = propertiesElement.getAttribute("version");
        if (xmlVersion.compareTo(EXTERNAL_XML_VERSION) > 0) throw new InvalidPropertiesFormatException("Exported Properties file format version " + xmlVersion + " is not supported. This java installation can read" + " versions " + EXTERNAL_XML_VERSION + " or older. You" + " may need to install a newer version of JDK.");
        importProperties(props, propertiesElement);
    }
    
    static Document getLoadingDoc(InputStream in) throws SAXException, IOException {
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setIgnoringElementContentWhitespace(true);
        dbf.setValidating(true);
        dbf.setCoalescing(true);
        dbf.setIgnoringComments(true);
        try {
            DocumentBuilder db = dbf.newDocumentBuilder();
            db.setEntityResolver(new XMLUtils$Resolver(null));
            db.setErrorHandler(new XMLUtils$EH(null));
            InputSource is = new InputSource(in);
            return db.parse(is);
        } catch (ParserConfigurationException x) {
            throw new Error(x);
        }
    }
    
    static void importProperties(Properties props, Element propertiesElement) {
        NodeList entries = propertiesElement.getChildNodes();
        int numEntries = entries.getLength();
        int start = numEntries > 0 && entries.item(0).getNodeName().equals("comment") ? 1 : 0;
        for (int i = start; i < numEntries; i++) {
            Element entry = (Element)(Element)entries.item(i);
            if (entry.hasAttribute("key")) {
                Node n = entry.getFirstChild();
                String val = (n == null) ? "" : n.getNodeValue();
                props.setProperty(entry.getAttribute("key"), val);
            }
        }
    }
    
    static void save(Properties props, OutputStream os, String comment, String encoding) throws IOException {
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = null;
        try {
            db = dbf.newDocumentBuilder();
        } catch (ParserConfigurationException pce) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
        Document doc = db.newDocument();
        Element properties = (Element)(Element)doc.appendChild(doc.createElement("properties"));
        if (comment != null) {
            Element comments = (Element)(Element)properties.appendChild(doc.createElement("comment"));
            comments.appendChild(doc.createTextNode(comment));
        }
        Set keys = props.keySet();
        Iterator i = keys.iterator();
        while (i.hasNext()) {
            String key = (String)(String)i.next();
            Element entry = (Element)(Element)properties.appendChild(doc.createElement("entry"));
            entry.setAttribute("key", key);
            entry.appendChild(doc.createTextNode(props.getProperty(key)));
        }
        emitDocument(doc, os, encoding);
    }
    
    static void emitDocument(Document doc, OutputStream os, String encoding) throws IOException {
        TransformerFactory tf = TransformerFactory.newInstance();
        Transformer t = null;
        try {
            t = tf.newTransformer();
            t.setOutputProperty(OutputKeys.DOCTYPE_SYSTEM, PROPS_DTD_URI);
            t.setOutputProperty(OutputKeys.INDENT, "yes");
            t.setOutputProperty(OutputKeys.METHOD, "xml");
            t.setOutputProperty(OutputKeys.ENCODING, encoding);
        } catch (TransformerConfigurationException tce) {
            if (!$assertionsDisabled) throw new AssertionError();
        }
        DOMSource doms = new DOMSource(doc);
        StreamResult sr = new StreamResult(os);
        try {
            t.transform(doms, sr);
        } catch (TransformerException te) {
            IOException ioe = new IOException();
            ioe.initCause(te);
            throw ioe;
        }
    }
    {
    }
    {
    }
}
