package navmid.parser;
import javax.xml.parsers.*;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.NodeList;
import org.xml.sax.EntityResolver;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;
import org.xml.sax.SAXParseException;

import edu.umd.cs.findbugs.annotations.CheckForNull;

import java.util.List;
import java.util.ArrayList;
import java.io.*;

/**
 * Parsing of a file given back by NavStatic (previous versions used Matos for
 * this).
 * @author piac6784
 *
 */
public class AnalysisFile {
	
    /**
     * The URI of the DTD of result files
     */
    final public static String NAVRES_DTD = "http://rd.francetelecom.com/matres.dtd";

	/**
	 * The name of the midlet node in analysis file
	 */
	final public static String  KW_MIDLET = "midlet";
	  
    /**
     * Auxiliary class that resolves the DTD of the result file if one is
     * specified.
     * @author piac6784
     *
     */
    static public class DtdResolver implements EntityResolver {
    	public InputSource resolveEntity (String publicId, String systemId) {
    		if (systemId.equals(NAVRES_DTD)) {
    			InputStream dtdStream =  this.getClass().getResourceAsStream("rules.dtd");
				return new InputSource(dtdStream);
    		} else return null;
    	}
    }
 
    /**
     * The root of the DOM tree describing the analysis file.
     */
    @CheckForNull
    private Element root = null;
    
    /**
     * The constructor initializes the SAX parser.
     * @param filename
     * @param midletname
     */
    public AnalysisFile(String filename, String midletname) {
    	try {
    		DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
    		DocumentBuilder docbuild = factory.newDocumentBuilder();
    		docbuild.setEntityResolver(new DtdResolver());
    		InputSource is = new InputSource(new FileReader(filename));
    		is.setEncoding("utf-8");

    		Document doc = docbuild.parse(is);
    		root = findRootMidlet(doc, midletname);
    		
    	} catch (SAXParseException e) {
    		System.err.println("Syntax error at " +  e.getLineNumber() + " - " +
    			   e.getColumnNumber() + " Entity " + e.getPublicId());
    	} catch (SAXException e) {
			System.err.println("Incorrect result file: " + e.getMessage());
		} catch (IOException e) {
			System.err.println("Cannot find the result file: " + e.getMessage());
		} catch (ParserConfigurationException e) {
			// Should not happen. 
			assert false;
		}
    }

    /**
     * Interprets the parsing of the file. 
     * The methods called will fill their internal tables 
     * with the result of the analysis.
     */
    public void parse () {
    	if (root == null) return;
    	NodeParser nodeParser = new NodeParser(root);
		RelationParser relationParser = new RelationParser(root, nodeParser);
		ControlParser controlParser = new ControlParser(nodeParser, relationParser);
		controlParser.buildTests(root);
		controlParser.buildCallbacks(root);
    }
    
    /**
     * Finds the midlet to analyze. A result file may contain several analyzed
     * midlets (this was definitely true with Matos. There is no reason to have
     * such a behaviour with NavStatic).
     * @param doc The document representing the analyzed file.
     * @param midletname The name of the midlet
     * @return The DOM element corresponding to the midlet.
     */
    @CheckForNull
    public Element findRootMidlet(Document doc, String midletname) {
    	List<Element> midlets = getElements(doc.getDocumentElement(),KW_MIDLET);

    	if (midletname == null) {
    		if (midlets.size() != 1) {
    			StringBuffer buf = new StringBuffer();
    			boolean cont = false;
    			for (Element m : midlets) {
    				if (cont) buf.append(",");
    				else cont=true;
    				buf.append(m.getAttribute("name"));
    			}

    			System.err.println("Select a midlet among " + buf + " with the -m option.");
    			return null;
    		} else return midlets.get(0);
    	} else {
    		for(Element m:midlets) {
    			if (m.getAttribute("name").equals(midletname)) return m;
    		}
    		System.err.println("Midlet " + midletname + " not found in the results of the analysis.");
    		return null;
    	}
    }
    
    /**
     * Given a DOM element e and an XML node name, gives back all the elements
     * immediate son of e and with the given name.
     * @param e the node to explore
     * @param name the name of the elements we look for.
     * @return a list of elements
     */
    public static List <Element> getElements(Element e, String name) {
    	List <Element> r = new ArrayList <Element>();
    	if (e.getNodeName().equals(name)) r.add(e);
    	else {
    		NodeList listNodes = e.getElementsByTagName(name);
    		int l = listNodes.getLength();
    		for(int i=0; i < l; i++)
    			r.add((Element) listNodes.item(i));
    	}
    	return r;
    }

    /**
     * Gives back all the XML nodes bellow a given node.
     * @param e the node to explore
     * @return the list of all its sons
     */
    public static Element [] getAllElements(Element e) {
    	NodeList listNodes = e.getChildNodes();
    	int l = listNodes.getLength();
    	ArrayList <Element> r = new ArrayList <Element> ();
    	for(int i=0; i < l; i++) 
    		if (listNodes.item(i) instanceof Element) {
    			r.add((Element) listNodes.item(i));
    		}
    	return r.toArray(new Element [0]);
    }
 
}
