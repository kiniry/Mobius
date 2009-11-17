package java.util.prefs;

import java.util.*;
import java.io.*;
import javax.xml.parsers.*;
import javax.xml.transform.*;
import javax.xml.transform.dom.*;
import javax.xml.transform.stream.*;
import org.xml.sax.*;
import org.w3c.dom.*;

class XmlSupport {
    {
    }
    
    XmlSupport() {
        
    }
    private static final String PREFS_DTD_URI = "http://java.sun.com/dtd/preferences.dtd";
    private static final String PREFS_DTD = "<?xml version=\"1.0\" encoding=\"UTF-8\"?><!-- DTD for preferences --><!ELEMENT preferences (root) ><!ATTLIST preferences EXTERNAL_XML_VERSION CDATA \"0.0\"  ><!ELEMENT root (map, node*) ><!ATTLIST root          type (system|user) #REQUIRED ><!ELEMENT node (map, node*) ><!ATTLIST node          name CDATA #REQUIRED ><!ELEMENT map (entry*) ><!ATTLIST map  MAP_XML_VERSION CDATA \"0.0\"  ><!ELEMENT entry EMPTY ><!ATTLIST entry          key CDATA #REQUIRED          value CDATA #REQUIRED >";
    private static final String EXTERNAL_XML_VERSION = "1.0";
    private static final String MAP_XML_VERSION = "1.0";
    
    static void export(OutputStream os, final Preferences p, boolean subTree) throws IOException, BackingStoreException {
        if (((AbstractPreferences)(AbstractPreferences)p).isRemoved()) throw new IllegalStateException("Node has been removed");
        Document doc = createPrefsDoc("preferences");
        Element preferences = doc.getDocumentElement();
        preferences.setAttribute("EXTERNAL_XML_VERSION", EXTERNAL_XML_VERSION);
        Element xmlRoot = (Element)(Element)preferences.appendChild(doc.createElement("root"));
        xmlRoot.setAttribute("type", (p.isUserNode() ? "user" : "system"));
        List ancestors = new ArrayList();
        for (Preferences kid = p, dad = kid.parent(); dad != null; kid = dad, dad = kid.parent()) {
            ancestors.add(kid);
        }
        Element e = xmlRoot;
        for (int i = ancestors.size() - 1; i >= 0; i--) {
            e.appendChild(doc.createElement("map"));
            e = (Element)(Element)e.appendChild(doc.createElement("node"));
            e.setAttribute("name", ((Preferences)(Preferences)ancestors.get(i)).name());
        }
        putPreferencesInXml(e, doc, p, subTree);
        writeDoc(doc, os);
    }
    
    private static void putPreferencesInXml(Element elt, Document doc, Preferences prefs, boolean subTree) throws BackingStoreException {
        Preferences[] kidsCopy = null;
        String[] kidNames = null;
        synchronized (((AbstractPreferences)(AbstractPreferences)prefs).lock) {
            if (((AbstractPreferences)(AbstractPreferences)prefs).isRemoved()) {
                elt.getParentNode().removeChild(elt);
                return;
            }
            String[] keys = prefs.keys();
            Element map = (Element)(Element)elt.appendChild(doc.createElement("map"));
            for (int i = 0; i < keys.length; i++) {
                Element entry = (Element)(Element)map.appendChild(doc.createElement("entry"));
                entry.setAttribute("key", keys[i]);
                entry.setAttribute("value", prefs.get(keys[i], null));
            }
            if (subTree) {
                kidNames = prefs.childrenNames();
                kidsCopy = new Preferences[kidNames.length];
                for (int i = 0; i < kidNames.length; i++) kidsCopy[i] = prefs.node(kidNames[i]);
            }
        }
        if (subTree) {
            for (int i = 0; i < kidNames.length; i++) {
                Element xmlKid = (Element)(Element)elt.appendChild(doc.createElement("node"));
                xmlKid.setAttribute("name", kidNames[i]);
                putPreferencesInXml(xmlKid, doc, kidsCopy[i], subTree);
            }
        }
    }
    
    static void importPreferences(InputStream is) throws IOException, InvalidPreferencesFormatException {
        try {
            Document doc = loadPrefsDoc(is);
            String xmlVersion = ((Element)(Element)doc.getChildNodes().item(1)).getAttribute("EXTERNAL_XML_VERSION");
            if (xmlVersion.compareTo(EXTERNAL_XML_VERSION) > 0) throw new InvalidPreferencesFormatException("Exported preferences file format version " + xmlVersion + " is not supported. This java installation can read" + " versions " + EXTERNAL_XML_VERSION + " or older. You may need" + " to install a newer version of JDK.");
            Element xmlRoot = (Element)(Element)doc.getChildNodes().item(1).getChildNodes().item(0);
            Preferences prefsRoot = (xmlRoot.getAttribute("type").equals("user") ? Preferences.userRoot() : Preferences.systemRoot());
            ImportSubtree(prefsRoot, xmlRoot);
        } catch (SAXException e) {
            throw new InvalidPreferencesFormatException(e);
        }
    }
    
    private static Document createPrefsDoc(String qname) {
        try {
            DOMImplementation di = DocumentBuilderFactory.newInstance().newDocumentBuilder().getDOMImplementation();
            DocumentType dt = di.createDocumentType(qname, null, PREFS_DTD_URI);
            return di.createDocument(null, qname, dt);
        } catch (ParserConfigurationException e) {
            throw new AssertionError(e);
        }
    }
    
    private static Document loadPrefsDoc(InputStream in) throws SAXException, IOException {
        XmlSupport$Resolver r = new XmlSupport$Resolver(null);
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        dbf.setIgnoringElementContentWhitespace(true);
        dbf.setValidating(true);
        dbf.setCoalescing(true);
        dbf.setIgnoringComments(true);
        try {
            DocumentBuilder db = dbf.newDocumentBuilder();
            db.setEntityResolver(new XmlSupport$Resolver(null));
            db.setErrorHandler(new XmlSupport$EH(null));
            return db.parse(new InputSource(in));
        } catch (ParserConfigurationException e) {
            throw new AssertionError(e);
        }
    }
    
    private static final void writeDoc(Document doc, OutputStream out) throws IOException {
        try {
            Transformer t = TransformerFactory.newInstance().newTransformer();
            t.setOutputProperty(OutputKeys.DOCTYPE_SYSTEM, doc.getDoctype().getSystemId());
            t.transform(new DOMSource(doc), new StreamResult(out));
        } catch (TransformerException e) {
            throw new AssertionError(e);
        }
    }
    
    private static void ImportSubtree(Preferences prefsNode, Element xmlNode) {
        NodeList xmlKids = xmlNode.getChildNodes();
        int numXmlKids = xmlKids.getLength();
        Preferences[] prefsKids;
        synchronized (((AbstractPreferences)(AbstractPreferences)prefsNode).lock) {
            if (((AbstractPreferences)(AbstractPreferences)prefsNode).isRemoved()) return;
            Element firstXmlKid = (Element)(Element)xmlKids.item(0);
            ImportPrefs(prefsNode, firstXmlKid);
            prefsKids = new Preferences[numXmlKids - 1];
            for (int i = 1; i < numXmlKids; i++) {
                Element xmlKid = (Element)(Element)xmlKids.item(i);
                prefsKids[i - 1] = prefsNode.node(xmlKid.getAttribute("name"));
            }
        }
        for (int i = 1; i < numXmlKids; i++) ImportSubtree(prefsKids[i - 1], (Element)(Element)xmlKids.item(i));
    }
    
    private static void ImportPrefs(Preferences prefsNode, Element map) {
        NodeList entries = map.getChildNodes();
        for (int i = 0, numEntries = entries.getLength(); i < numEntries; i++) {
            Element entry = (Element)(Element)entries.item(i);
            prefsNode.put(entry.getAttribute("key"), entry.getAttribute("value"));
        }
    }
    
    static void exportMap(OutputStream os, Map map) throws IOException {
        Document doc = createPrefsDoc("map");
        Element xmlMap = doc.getDocumentElement();
        xmlMap.setAttribute("MAP_XML_VERSION", MAP_XML_VERSION);
        for (Iterator i = map.entrySet().iterator(); i.hasNext(); ) {
            Map$Entry e = (Map$Entry)(Map$Entry)i.next();
            Element xe = (Element)(Element)xmlMap.appendChild(doc.createElement("entry"));
            xe.setAttribute("key", (String)(String)e.getKey());
            xe.setAttribute("value", (String)(String)e.getValue());
        }
        writeDoc(doc, os);
    }
    
    static void importMap(InputStream is, Map m) throws IOException, InvalidPreferencesFormatException {
        try {
            Document doc = loadPrefsDoc(is);
            Element xmlMap = (Element)(Element)doc.getChildNodes().item(1);
            String mapVersion = xmlMap.getAttribute("MAP_XML_VERSION");
            if (mapVersion.compareTo(MAP_XML_VERSION) > 0) throw new InvalidPreferencesFormatException("Preferences map file format version " + mapVersion + " is not supported. This java installation can read" + " versions " + MAP_XML_VERSION + " or older. You may need" + " to install a newer version of JDK.");
            NodeList entries = xmlMap.getChildNodes();
            for (int i = 0, numEntries = entries.getLength(); i < numEntries; i++) {
                Element entry = (Element)(Element)entries.item(i);
                m.put(entry.getAttribute("key"), entry.getAttribute("value"));
            }
        } catch (SAXException e) {
            throw new InvalidPreferencesFormatException(e);
        }
    }
    {
    }
    {
    }
}
