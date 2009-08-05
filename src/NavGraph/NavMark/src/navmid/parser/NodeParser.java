package navmid.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import navmid.graph.CallbackNode;
import navmid.graph.CommandNode;
import navmid.graph.DisplayableNode;
import navmid.graph.ItemNode;
import navmid.graph.ListenerAssociationNode;
import navmid.graph.ListenerNode;
import navmid.graph.Node;
import navmid.graph.DisplayableNode.DisplayableKind;
import navmid.ui.Main;

import org.w3c.dom.Element;

import javax.annotation.CheckForNull;


/**
 * Parsing of node descriptions in result files given back by navstat (previously by Matos).
 * @author piac6784
 *
 */
public class NodeParser {

	private final boolean debug = Main.debug;
	/**
	 * Global map of all known abstractions of Displayable objects
	 */
	private HashMap<Integer,DisplayableNode> displayableMap =
    	new HashMap<Integer,DisplayableNode> ();

	/**
	 * Global map of all known abstractions of Command (Events) objects
	 */
    private HashMap<Integer,CommandNode> commandMap =
    	new HashMap<Integer,CommandNode> ();

	/**
	 * Global map of all known abstractions of Listeners (callbacks) objects
	 */
    private HashMap<Integer,ListenerNode> listenerMap =
    	new HashMap<Integer,ListenerNode> ();

	/**
	 * Global map of all known abstractions of Items (components of displaybles) objects
	 */
    private HashMap<Integer,ItemNode> itemMap =
    	new HashMap<Integer,ItemNode> ();

    
    /**
     * Parses the node object and explore their defined classes and interfaces to register the
     * object abstractions in the right category. Some links are already initiated at that level
     * @param root the root node of the document (DOM object) containing the result of the navstat
     * analysis.
     */
    NodeParser(Element root) {
    	List <Element> nodes = AnalysisFile.getElements(root,"node");
    	for(Element elt : nodes) {
    		Integer id = Integer.valueOf(elt.getAttribute("id"));
    		List <Element> classes = AnalysisFile.getElements(elt,"class");
    		List <String> classNames = new ArrayList <String> ();
    		for(Element clazz: classes) classNames.add(clazz.getAttribute("name"));
  
    		String actual_class = classNames.get(0);
    		loop : for(String classname : classNames) {
    			if (classname.equals("javax.microedition.lcdui.List")) {
    				displayable(id,new DisplayableNode(DisplayableKind.LIST,id, classNames));
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.Alert")) {
    				displayable(id,new DisplayableNode(DisplayableKind.ALERT,id, classNames));
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.Form")) {
    				displayable(id,new DisplayableNode(DisplayableKind.FORM,id, classNames));
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.TextBox")) {
    				displayable(id,new DisplayableNode(DisplayableKind.TEXTBOX,id, classNames));
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.Canvas")) {
    				ListenerNode ln = new ListenerNode(actual_class,id);
    				DisplayableNode dn =new DisplayableNode(DisplayableKind.CANVAS,id, classNames); 
    				displayable(id,dn);
       				listener(id,ln);
       				ListenerAssociationNode.link(dn,ln,CallbackNode.Event.CANVAS);
    				break loop;
    			} else if (classname.equals("javax.microedition.midlet.MIDlet")) {
    				ListenerNode ln = new ListenerNode(actual_class,id);
    				listener(id,ln);
       				ListenerAssociationNode.link(DisplayableNode.start,ln,CallbackNode.Event.START);
       				ListenerAssociationNode.link(DisplayableNode.start,ln,CallbackNode.Event.INIT);
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.Command")) {
    				command(id, new CommandNode(id.intValue()));
    				break loop;
    			} else if (classname.equals("javax.microedition.lcdui.ChoiceGroup")) {
    				item(id, new ItemNode(ItemNode.ItemKind.CHOICE_GROUP));
    			} else if (classname.equals("javax.microedition.lcdui.DateField")) {
    				item(id, new ItemNode(ItemNode.ItemKind.DATE));
    			} else if (classname.equals("javax.microedition.lcdui.Gauge")) {
    				item(id, new ItemNode(ItemNode.ItemKind.GAUGE));
    			} else if (classname.equals("javax.microedition.lcdui.ImageItem")) {
    				item(id, new ItemNode(ItemNode.ItemKind.IMAGE_ITEM));
    			} else if (classname.equals("javax.microedition.lcdui.Spacer")) {
    				item(id, new ItemNode(ItemNode.ItemKind.SPACER));
    			} else if (classname.equals("javax.microedition.lcdui.StringItem")) {
    				item(id, new ItemNode(ItemNode.ItemKind.STRING_ITEM));
    			} else if (classname.equals("javax.microedition.lcdui.TextField")) {
    				item(id, new ItemNode(ItemNode.ItemKind.TEXT_FIELD));
    			}
    		}
    	
    		for(Element clazz : AnalysisFile.getElements(elt,"interface")) {
    			String classname = clazz.getAttribute("name");
    			if (classname.equals("javax.microedition.lcdui.CommandListener") ||
    					classname.equals("javax.microedition.lcdui.ItemCommandListener") ||
    					classname.equals("javax.microedition.lcdui.ItemStateChangedListener")) { 
    				listener(id,new ListenerNode(actual_class,id));
    			}

    		}
    	}
    }

    /**
     * Register a Displayable object.
     * @param id number identifying the object in the result file
     * @param node internal representation of the object in NavMark.
     */
    void displayable(Integer id, DisplayableNode node) {
    	if (debug) System.err.println("Put " + node );
		displayableMap.put(id, node);
	}

    /**
     * Register a Command object.
     * @param id number identifying the object in the result file
     * @param node internal representation of the object in NavMark.
     */
	void command(Integer id, CommandNode node) {
		if (debug) System.err.println("Put " + node );
		commandMap.put(id, node);
	}
	
    /**
     * Register a Listener object.
     * @param id number identifying the object in the result file
     * @param node internal representation of the object in NavMark.
     */
	void listener(Integer id, ListenerNode node) {
		listenerMap.put(id, node);
	}
	
    /**
     * Register an Item object.
     * @param id number identifying the object in the result file
     * @param node internal representation of the object in NavMark.
     */
	void item(Integer id, ItemNode node) {
		itemMap.put(id,node);
	}

	
	/**
	 * Find back the representation of an object in one of the three maps (not working for items)
	 * @param i the id of the object in the navstat result file.
	 * @return the node found or null if in none of the categories.
	 */
	@CheckForNull
	Node getNode(Integer i) {
		Node r = displayableMap.get(i);
		if (r != null) return r;
		r = commandMap.get(i);
		if (r != null) return r;
		r = listenerMap.get(i);
		return r;
	}
	
	/**
	 * This generic function is used to parse an element describing the values for an argument of a call analysis (result of a points-to).
	 * It is used for generic object results.
	 * 
	 * @param <E> type parameter describing the kind on element we are trying to find
	 * @param e The element of the DOM tree of the result file we are parsing
	 * @param map a map translating refnode references in actual graph nodes.
	 * @param res The list where we store the elements found 
	 */
	private <E> void getElement(Element e, HashMap<Integer,E> map, List<E> res) {
		String name = e.getNodeName();
		if(name.equals("refnode")) {
			E elt = map.get(Integer.valueOf(e.getAttribute("id")));
			if(elt==null) { System.err.println("PB: " + e.getAttribute("id"));}
			else res.add(elt);
		}
		else if (name.equals("or")) {
			for(Element son: AnalysisFile.getAllElements(e)) {
				getElement(son, map, res);
			}
		}
	}
	
	/**
	 * This functions parse  an element describing the values for an argument of a call analysis (result of a points-to) when strings
	 * are expected.
	 * @param e The element to parse.
	 * @return The list of potential strings found or null if there is an element we cannot analyze (any string)
	 */
	@CheckForNull
	List <String> getStrings(Element e) {
		List<String> res = new ArrayList<String>();
		String name = e.getNodeName();
		if(name.equals("string")) 
			res.add(e.getAttribute("value"));
		else if (name.equals("or")) {
			for(Element son: AnalysisFile.getAllElements(e)) {
				List <String> vals = getStrings(son);
				if (vals == null) return null;
				res.addAll(vals);
			}
		} else return null;
		return res;
	}
	
	/**
	 * This functions parse  an element describing the values for an argument of a call analysis (result of a points-to) when strings
	 * are expected.
	 * @param e The element of the result DOM tree to parse.
	 * @return The list of potential integers found or null if there is an element we cannot analyze.
	 */ 
	@CheckForNull
	List <Integer> getIntegers(Element e) {
		List<Integer> res = new ArrayList<Integer>();
		String name = e.getNodeName();
		if(name.equals("literal")) 
			res.add(Integer.valueOf(e.getAttribute("value")));
		else if (name.equals("or")) {
			for(Element son: AnalysisFile.getAllElements(e)) {
				List <Integer> vals = getIntegers(son);
				if (vals==null) return null;
				res.addAll(vals);
			}
		} else return null;
		return res;
	}
	
	/**
	 * Parse an argument result consisting of Command values
	 * @param e The element of the result DOM tree to parse.
	 * @return The list of commands found
	 */
	List <CommandNode> getCommand(Element e) {
		ArrayList <CommandNode> res = new ArrayList <CommandNode> ();
		getElement(e, commandMap, res);
		return res;
	}
	
	/**
	 * Parse an argument result consisting of Displayable values
	 * @param e The element of the result DOM tree to parse.
	 * @return the list of displayable found.
	 */
	List <DisplayableNode> getDisplayable(Element e) {
		ArrayList <DisplayableNode> res = new ArrayList <DisplayableNode> ();
		getElement(e, displayableMap, res);
		return res;
	}
	
	/**
	 * Parse an argument result consisting of Listener values
	 * @param e The element of the result DOM tree to parse.
	 * @return the list of listener found.
	 */
	List <ListenerNode> getListener(Element e) {
		ArrayList <ListenerNode> res = new ArrayList <ListenerNode> ();
		getElement(e, listenerMap, res);
		return res;
	}

	/**
	 * Parse an argument result consisting of Items values
	 * @param e The element of the result DOM tree to parse.
	 * @return the list of items found.
	 */
	List <ItemNode> getItem(Element e) {
		ArrayList <ItemNode> res = new ArrayList <ItemNode> ();
		getElement(e, itemMap, res);
		return res;
	}

	
}
