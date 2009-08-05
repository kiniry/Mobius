package navmid.parser;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import navmid.graph.ActionNode;
import navmid.graph.CallbackNode;
import navmid.graph.ListenerClassNode;
import navmid.graph.ListenerNode;
import navmid.graph.Node;
import navmid.graph.PathNode;
import navmid.graph.TestNode;
import navmid.graph.CallbackNode.Event;
import navmid.graph.Node.Kind;

import org.w3c.dom.Element;

public class ControlParser {
	
	private static final String [] FORBIDDEN_PREFIXES = {
		"java.", "javax.", "com.francetelecom.rd.fakemidp."
	};
	private static final String KW_OR = "or";
	private static final String KW_REFNODE = "refnode";
	private static final String KW_ACTION = "event";
	private static final String KW_PARAMETER = "parameter";
	private static final String KW_TEST = "test";
	private static final String KW_BRANCH = "branch";
	private static final String KW_BRANCHREF = "branchref";
	private static final String KW_PATH = "path";
	private static final String KW_SETTER = "setterref";
	final public static String	KW_COM_ACTION = "callback";

	private static final String AT_START = "start";
	private static final String AT_ID = "id";
	private static final String AT_SYMBOL = "symbol";
	private static final String AT_POS = "pos";
	private static final String AT_METHOD = "method";
	private static final String AT_EXTENDS = "extends";
	private static final String AT_CLASS = "class";
	
	private final NodeParser nodeParser;
	private final RelationParser relationParser;
    /**
     * This map translates branch reference in TestNode objects.
     */
    private HashMap<Integer,TestNode> testMap = new HashMap<Integer,TestNode> ();
    
    /**
     * Builds the parser for callbacks based on the analysis of available nodes and the
     * relations between those nodes (for mark infos).
     * @param np analysis of nodes;
     * @param rp analysis of relations.
     */
    ControlParser(NodeParser np, RelationParser rp) {
    	nodeParser=np;
    	relationParser=rp;
    }

    /**
     * Parses test description (node with name branch)
     * @param root The "midlet" DOM element containing the descriptions
     */
    void buildTests(Element root) {
    	test_loop : for(Element elt: AnalysisFile.getElements(root,KW_BRANCH)) {
    		Element contents = (Element) elt.getChildNodes().item(1);
    		Integer id = Integer.valueOf(elt.getAttribute(AT_ID));
    		String name = contents.getNodeName();
    		if(name.equals(KW_TEST)) {
    			Set <Object> potential = new HashSet <Object> ();
    			int position;
    			String test = contents.getAttribute(AT_SYMBOL);
    			Element [] args = AnalysisFile.getAllElements(contents);
    			if (args.length != 2) continue test_loop;
    			if (args[0].getNodeName().equals(KW_PARAMETER)) {
    				position = Integer.parseInt(args[0].getAttribute(AT_POS));
    				parseArg(potential, args[1]);
    			} else if(args[1].getNodeName().equals(KW_PARAMETER)) {
    				position = Integer.parseInt(args[1].getAttribute(AT_POS));
    				parseArg(potential, args[0]);
    			} else continue test_loop;
    			TestNode b = new TestNode(test, position, potential);
    			testMap.put(id,b);
    		}
    	}
    }
    
    /**
     * Parses test arguments which are reference to nodes.
     * @param pot A buffer set to accumulate potential values.
     * @param arg The DOM element containing the description of potential values.
     */
    private void parseArg(Set <Object> pot, Element arg) {
    	String name = arg.getNodeName();
    	if(name.equals(KW_REFNODE)) {
    		Integer i = Integer.valueOf(arg.getAttribute(AT_ID));
    		Node r = nodeParser.getNode(i);
    		if (r != null) pot.add(r);
    	} else if (name.equals(KW_OR)) {
    		for(Element son: AnalysisFile.getAllElements(arg)) parseArg(pot,son);
    	}
    }
    
    /**
     * Parses callback descriptions (nodes named "callback")
     * @param root The "midlet" DOM element containing the descriptions.
     */
    void buildCallbacks(Element root) {
    	HashMap<String, ListenerClassNode> pool = new HashMap <String, ListenerClassNode> ();
    	List <Element> nodes = AnalysisFile.getElements(root,KW_COM_ACTION);
    	callback_loop: for(Element callback: nodes) {
    		String clazz = callback.getAttribute(AT_CLASS);
    		if (clazz == null) continue callback_loop;
    		for(String prefix: FORBIDDEN_PREFIXES)
    			if (clazz.startsWith(prefix)) continue callback_loop;
    		String template = callback.getAttribute(AT_EXTENDS);
    		String method = callback.getAttribute(AT_METHOD);
    		Event purpose = getPurpose(method,template);
    	
    		ListenerClassNode lcn = pool.get(clazz);
    		if(lcn == null) {
    			lcn = new ListenerClassNode(clazz);
    			pool.put(clazz, lcn);
    		}
    		CallbackNode node = new CallbackNode(purpose,method);
    		lcn.linkTo(node);
    		List <Element> actions = AnalysisFile.getElements(callback,KW_ACTION);		
    		Map <Integer, List <ActionNode>> actionMap = buildActionMap(actions);
    		buildPaths(node,actionMap,actions);
    	}
    	for(Node l:Node.all(Kind.LISTENER)) {
			ListenerNode listener = (ListenerNode) l;
			ListenerClassNode cb = pool.get(listener.clazz);
			listener.linkTo(cb);
		}
    }
    
    /**
     * From a callback method name and the definition of the template class, it identifies
     * the kind of events that are treated.
     * @param method the callback method
     * @param template the template class implemented by the class containing the callback
     * @return Formal description of the event as an Event object.
     */
    private Event getPurpose(String method, String template) {
		if (template.equals("javax.microedition.midlet.MIDlet")){
			if (method.equals("startApp")) return Event.START;
			else if (method.equals("destroyApp")) return Event.STOP;
			else return Event.INIT;
		} else if (template.equals("javax.microedition.lcdui.CommandListener")) {
			return Event.COMMAND;
		} else if (template.equals("javax.microedition.lcdui.Canvas")) {
			return Event.CANVAS;
		} else if (template.equals("javax.microedition.lcdui.ItemStateListener")) {
			return Event.ITEM_STATE;
		} else if (template.equals("java.lang.Thread")) {
			return Event.THREAD;
		} else return Event.UNDEFINED;
    }
    
    
    /**
     * Builds ActionNode objects associated to a callback and a map linking NavStatic Ids to 
     * those objects.
     * @param actions The list of DOM elements describing the actions.
     * @return The association map to be used by {@link #buildPaths(CallbackNode, Map, List)}
     */
    private Map <Integer, List <ActionNode>> buildActionMap (List <Element> actions) {
		Map <Integer, List <ActionNode>> actionMap = new HashMap<Integer, List <ActionNode>> ();
		for (Element action : actions) {
			Integer idAction = Integer.valueOf(action.getAttribute(AT_ID));
			List <Element> setterList = AnalysisFile.getElements(action, KW_SETTER);
			if (setterList.size() > 0) {
				List <ActionNode> lan = new ArrayList <ActionNode> ();
				for(Element setter: setterList) {
					Integer id_setter = Integer.valueOf(setter.getAttribute(AT_ID));
	    			ActionNode actionNode = relationParser.getAction(id_setter);
	    			if (actionNode != null) lan.add(actionNode);
	    			else {
	    				System.err.println("Cannot find actionNode for " + idAction);    	    				
	    			}
				}
				if (lan.size() > 0) actionMap.put(idAction, lan); 
			}
		}
		return actionMap;
    }
    
    /**
     * Build the paths of a callback
     * @param node The callback node for which we are building the paths
     * @param actionMap A map translating action ids in actual ActionNode.
     * @param actions the list of DOM elements describing actions for this callback.
     */
    private void buildPaths(CallbackNode node,
    		Map <Integer, List <ActionNode>> actionMap,
    		List <Element> actions) {
		action_loop : for (Element action : actions) {
			Integer id_action = Integer.valueOf(action.getAttribute(AT_ID));
			List <ActionNode> actionNodeList = actionMap.get(id_action);
			if (actionNodeList == null) continue action_loop;
			List <Element> paths = AnalysisFile.getElements(action,KW_PATH);
			for(Element path: paths) {
				PathNode pathNode = new PathNode();
				Integer idActionOrigin = Integer.valueOf(path.getAttribute(AT_START));
				List <ActionNode> originNodeList = actionMap.get(idActionOrigin);
				if(originNodeList != null) {
					for(ActionNode originNode:originNodeList) originNode.linkTo(pathNode);
				}
				for(ActionNode actionNode: actionNodeList) pathNode.linkTo(actionNode);
				List<Element> branchrefs = AnalysisFile.getElements(path,KW_BRANCHREF);
				for(Element branchref: branchrefs) {
					Integer idb = Integer.valueOf(branchref.getAttribute(AT_ID));
					TestNode b = testMap.get(idb);
					if (b != null) {
						b = (branchref.getAttribute(AT_POS).equals("Y")) ? b.negate() : b;
						pathNode.linkTo(b);
					}
				}
				node.linkTo(pathNode);
			}
		}
    }

}
