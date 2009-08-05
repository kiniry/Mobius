package navmid.parser;

import java.util.HashMap;
import java.util.List;

import navmid.graph.ActionNode;
import navmid.graph.CallbackNode;
import navmid.graph.CommandNode;
import navmid.graph.DisplayableNode;
import navmid.graph.ItemNode;
import navmid.graph.ListenerAssociationNode;
import navmid.graph.ListenerNode;
import navmid.graph.Node;
import navmid.graph.ObjectNode;
import navmid.graph.StringNode;

import org.w3c.dom.Element;

import javax.annotation.CheckForNull;

public class RelationParser {
	static final String MARK_ATTR = "mark"; // was lcdui

	/**
	 * This enumeration represents all the relations recorded by navstatic and used by navmark.
	 * We use the valueOf trick to get an enumeration element from a string containing the name
	 * of the element. This puts some restrictions on the naming of relations in navstatic.
	 * Errors are handled with the error element.
	 * @author piac6784
	 *
	 */
	public enum Relation {
		DISPLAYABLE_ADD_COMMAND, DISPLAYABLE_SET_COMMAND_LISTENER, DISPLAYABLE_SET_TITLE,
		DISPLAYABLE_SET_TICKER,DISPLAYABLE_REMOVE_COMMAND,
		ALERT_NEW_1, ALERT_NEW_2, ALERT_SET_INDICATOR, ALERT_SET_STRING, ALERT_SET_IMAGE,
		ALERT_SET_TYPE, ALERT_SET_TIMEOUT, ALERT_PLAYSOUND, ALERT_SET_COMMAND_LISTENER,
		CHOICE_APPEND, CHOICE_INSERT, CHOICE_SET, CHOICE_DELETE, CHOICE_DELETE_ALL,
		CHOICE_SET_FONT, CHOICEGROUP_NEW_1, CHOICEGROUP_NEW_2, COMMAND_NEW_1, COMMAND_NEW_2,
		DATEFIELD_NEW_1, DATEFIELD_NEW_2, DISPLAY_SET_CURRENT_2, DISPLAY_SET_CURRENT_1,
		RETURN_FONT_DEFAULT, FONT_GETFONT_1, FONT_GETFONT_2, FORM_NEW_1, FORM_NEW_2,
		FORM_APPEND_1, FORM_APPEND_2, FORM_APPEND_3, FORM_SET_ITEM_STATE_LISTENER,
		GAUGE_NEW, GAUGE_SET_LABEL, RETURN_IMAGE_CREATE_1, RETURN_IMAGE_CREATE_2,
		RETURN_IMAGE_CREATE_3, RETURN_IMAGE_CREATE_4, RETURN_IMAGE_CREATE_5, IMAGEITEM_NEW_1,
		IMAGEITEM_NEW_2, IMAGEITEM_SET_IMAGE, IMAGEITEM_SET_ALTTEXT, IMAGEITEM_SET_LAYOUT,
		ITEM_ADD_COMMAND, ITEM_SET_DEFAULT_COMMAND, ITEM_SET_LABEL, ITEM_SET_LAYOUT,
		ITEM_SET_COMMANDLISTENER, LIST_NEW_1, LIST_NEW_2, LIST_APPEND, LIST_INSERT,
		LIST_SET, LIST_SET_SELECTCOMMAND, SPACER_NEW, SPACER_SET_LABEL,
		SPACER_SET_DEFAULT_COMMAND, STRINGITEM_NEW_1, STRINGITEM_NEW_2, STRINGITEM_SET_TEXT,
		STRINGITEM_SET_FONT, TEXTBOX_NEW, TEXTBOX_SET_CONSTRAINTS, TEXTFIELD_NEW,
		TEXTFIELD_SET_CONSTRAINTS, TICKER_NEW, TICKER_SET_STRING, CONNECTOR_OPEN_1,
		CONNECTOR_OPEN_2, CONNECTOR_OPEN_3, CONNECTOR_OPEN_DATAINPUT,
		CONNECTOR_OPEN_DATAOUTPUT, CONNECTOR_OPEN_INPUT, CONNECTOR_OPEN_OUTPUT,
		MIDLET_PLATFORMREQUEST, MESSAGECONNECTION_SEND, SMS_SEND_1, SMS_SEND_2, MIDLET_DESTROY,
		CANVAS_NEW,
		error;

		public static Relation c(String Str) {
			try {return valueOf(Str);} catch (Exception ex){return error;} 
		}
	}

	private HashMap<Integer,ActionNode> markToAction = new HashMap<Integer, ActionNode> ();

	@CheckForNull
	public ActionNode getAction(Integer id) { return markToAction.get(id); }

	private static void register_init(ObjectNode node, Element elt) {
		int offset = Integer.parseInt(elt.getAttribute("offset"));
		String method = elt.getAttribute("orig");
		node.set_origin(method,offset);
	}

	private static void register_action(ActionNode node, Element elt) {
		int offset = Integer.parseInt(elt.getAttribute("offset"));
		String method = elt.getAttribute("orig");
		node.set_origin(method,offset);
	}

	public RelationParser(Element root, NodeParser nodeParser) {
		for(Element elt : AnalysisFile.getElements(root,"args")) {
			String att  = elt.getAttribute("id");
			Relation id = Relation.c(att);
			// for(Element rel : AnalysisFile.getElements(elt,"and")) {
			Element args [] = AnalysisFile.getAllElements(elt);
			System.err.println(id);
			switch(id) {
			case DISPLAYABLE_ADD_COMMAND: {
				for(DisplayableNode disp: nodeParser.getDisplayable(args[0]))
					for(CommandNode com : nodeParser.getCommand(args[1])) disp.linkTo(com);
				break;
			}
			case DISPLAYABLE_SET_COMMAND_LISTENER:
			case ALERT_SET_COMMAND_LISTENER: {
				for(DisplayableNode disp: nodeParser.getDisplayable(args[0]))
					for(ListenerNode list : nodeParser.getListener(args[1])) 
						ListenerAssociationNode.link(disp,list,CallbackNode.Event.COMMAND);
				break;
			}
			case FORM_SET_ITEM_STATE_LISTENER: {
				for(DisplayableNode disp: nodeParser.getDisplayable(args[0]))
					for(ListenerNode list : nodeParser.getListener(args[1])) 
						ListenerAssociationNode.link(disp,list,CallbackNode.Event.ITEM_STATE);
				break;       				
			}
			case DISPLAY_SET_CURRENT_1: {
				try {
					Integer action_id = Integer.valueOf(elt.getAttribute(MARK_ATTR));
					ActionNode an = new ActionNode(ActionNode.ActionKind.SETDISPLAY);
					register_action(an,elt);
					for(Node n: nodeParser.getDisplayable(args[1])) an.linkTo(n);
					markToAction.put(action_id, an);
				} catch (Exception e) {e.printStackTrace();}
				break;
			}
			case MIDLET_DESTROY: {
				Integer action_id = Integer.valueOf(elt.getAttribute(MARK_ATTR));
				ActionNode an = new ActionNode(ActionNode.ActionKind.SETDISPLAY);
				register_action(an,elt);
				an.linkTo(DisplayableNode.stop);
				markToAction.put(action_id, an);
				break;
			}
			case COMMAND_NEW_1:
			case COMMAND_NEW_2: {
				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getCommand(args[0])) {
						register_init((ObjectNode) n,elt);
						StringNode attr = StringNode.getAndSet(n,"label");
						attr.add(labels);
					}
				}
				break;
			}
			case DISPLAYABLE_SET_TITLE: {
				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) { 
					for(Node n : nodeParser.getCommand(args[0])) {
						StringNode attr = StringNode.getAndSet(n,"title");
						attr.add(labels);
					}
				}
				break;
			}
			case DISPLAYABLE_SET_TICKER: {

				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getCommand(args[0])) {
						StringNode attr = StringNode.getAndSet(n,"ticker");
						attr.add(labels);
					}
				}
				break;
			}	
			case ALERT_NEW_2: {
				List <String> texts = nodeParser.getStrings(args[2]);
				if (texts != null) {
					for(Node n : nodeParser.getDisplayable(args[0])) {
						StringNode attr = StringNode.getAndSet(n,"text");
						attr.add(texts);
					}
				}
				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getDisplayable(args[0])) {
						register_init((ObjectNode) n,elt);
						StringNode attr = StringNode.getAndSet(n,"title");
						attr.add(labels);
					}
				}
				break;
			}    				
			case ALERT_NEW_1: {

				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getDisplayable(args[0])) {
						register_init((ObjectNode) n,elt);
						StringNode attr = StringNode.getAndSet(n,"title");
						attr.add(labels);
					}
				}
				break;
			}
			case CANVAS_NEW: {
				List <DisplayableNode> candidates = nodeParser.getDisplayable(args[0]);
				if (candidates.size() > 1) break;
				for(Node n : candidates) register_init((ObjectNode)n,elt);
				break;    				
			}

			case FORM_NEW_1: 
			case FORM_NEW_2: {
				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getDisplayable(args[0])) {
						register_init((ObjectNode)n,elt);
						StringNode attr = StringNode.getAndSet(n,"title");
						attr.add(labels);
					}
				}
				break;
			}
			case LIST_NEW_1: 
			case LIST_NEW_2: {
				List <String> labels = nodeParser.getStrings(args[1]);
				if (labels != null) {
					for(Node n : nodeParser.getDisplayable(args[0])) {
						register_init((ObjectNode)n,elt);
						StringNode attr = StringNode.getAndSet(n,"title");
						attr.add(labels);
					}
				}
				break;
			}

			case FORM_APPEND_1: {
				List <String> labels = nodeParser.getStrings(args[1]);
				ItemNode in = new ItemNode(ItemNode.ItemKind.STRING_ITEM);
				if (labels != null) {
					StringNode attr = StringNode.getAndSet(in,"text");
					attr.add(labels);
				}
				for(Node n : nodeParser.getDisplayable(args[0])) {
					n.linkTo(in);
				}
				for(DisplayableNode disp: nodeParser.getDisplayable(args[0]))
					for(ItemNode it : nodeParser.getItem(args[1])) disp.linkTo(it);
				break;
			}
			case FORM_APPEND_2: {
				for(DisplayableNode disp: nodeParser.getDisplayable(args[0]))
					for(ItemNode it : nodeParser.getItem(args[1])) disp.linkTo(it);
				break;
			}	
			case FORM_APPEND_3: {
				ItemNode in = new ItemNode(ItemNode.ItemKind.IMAGE_ITEM);
				for(Node n : nodeParser.getDisplayable(args[0])) n.linkTo(in);
				break;
			}
			case STRINGITEM_NEW_1:
			case STRINGITEM_NEW_2: {
				List <String> texts = nodeParser.getStrings(args[2]);
				List <String> labels = nodeParser.getStrings(args[1]);
				for(Node n : nodeParser.getItem(args[0])) {
					if (texts != null) {
						StringNode attr1 = StringNode.getAndSet(n,"text");
						attr1.add(texts);
					}
					if (labels != null) {
						StringNode attr2 = StringNode.getAndSet(n,"title");
						attr2.add(labels);
					}
				}
				break;

			}
			case STRINGITEM_SET_TEXT: {
				List <String> texts = nodeParser.getStrings(args[1]);
				if (texts != null) {
					for(Node n : nodeParser.getItem(args[0])) {
						StringNode attr1 = StringNode.getAndSet(n,"text");
						attr1.add(texts);
					}
				}
				break;
			}
			case ALERT_SET_INDICATOR:
			case ALERT_SET_STRING:
			case ALERT_SET_IMAGE:
			case ALERT_SET_TYPE:
			case ALERT_SET_TIMEOUT:
			case ALERT_PLAYSOUND:

			case CHOICE_APPEND:
			case CHOICE_INSERT:
			case CHOICE_SET: 
			case CHOICE_DELETE:
			case CHOICE_DELETE_ALL:
			case CHOICE_SET_FONT: 
			case CHOICEGROUP_NEW_1:
			case CHOICEGROUP_NEW_2:

			case DATEFIELD_NEW_1:
			case DATEFIELD_NEW_2:
			case DISPLAY_SET_CURRENT_2:

			case RETURN_FONT_DEFAULT:
			case FONT_GETFONT_1:
			case FONT_GETFONT_2: 

			case GAUGE_NEW: 
			case GAUGE_SET_LABEL: 
			case RETURN_IMAGE_CREATE_1: 
			case RETURN_IMAGE_CREATE_2:
			case RETURN_IMAGE_CREATE_3: 
			case RETURN_IMAGE_CREATE_4: 
			case RETURN_IMAGE_CREATE_5: 
			case IMAGEITEM_NEW_1:
			case IMAGEITEM_NEW_2: 
			case IMAGEITEM_SET_IMAGE: 
			case IMAGEITEM_SET_ALTTEXT: 
			case IMAGEITEM_SET_LAYOUT:
			case ITEM_ADD_COMMAND: 
			case ITEM_SET_DEFAULT_COMMAND: 
			case ITEM_SET_LABEL: 
			case ITEM_SET_LAYOUT:
			case ITEM_SET_COMMANDLISTENER: 
			case LIST_APPEND: 
			case LIST_INSERT:
			case LIST_SET: 
			case LIST_SET_SELECTCOMMAND: 
			case SPACER_NEW: 
			case SPACER_SET_LABEL:
			case SPACER_SET_DEFAULT_COMMAND: 


			case STRINGITEM_SET_FONT: 
			case TEXTBOX_NEW: 
			case TEXTBOX_SET_CONSTRAINTS: 
			case TEXTFIELD_NEW:
			case TEXTFIELD_SET_CONSTRAINTS:
			case TICKER_NEW:
			case TICKER_SET_STRING:
    			case CONNECTOR_OPEN_1:
    			case CONNECTOR_OPEN_2:
    			case CONNECTOR_OPEN_3:
    			case CONNECTOR_OPEN_DATAINPUT:
    			case CONNECTOR_OPEN_DATAOUTPUT:
    			case CONNECTOR_OPEN_INPUT:
    			case CONNECTOR_OPEN_OUTPUT:
    			case MIDLET_PLATFORMREQUEST:
    			case MESSAGECONNECTION_SEND:
    			case SMS_SEND_1: 
    			case SMS_SEND_2:
    			case DISPLAYABLE_REMOVE_COMMAND:	
    			default:	
    				break;
    			}
    		}
    	// }
    }
  
}
