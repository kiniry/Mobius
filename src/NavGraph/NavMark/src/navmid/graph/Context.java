package navmid.graph;

import java.util.ArrayList;
import java.util.List;

import navmid.graph.Node.Kind;

/**
 * This class describes an execution context for a callback. An execution context contains the potential 
 * arguments of the callback and is usually defined by the originating screen and the potential
 * commands linked to this screen for a commandAction. Other kinds of contexts are possible (for example
 * for an item and its commands).
 * @author piac6784
 *
 */
public class Context {
	/**
	 * The abstraction of the arguments. Each element of the array describe one potential argument.
	 */
	final private ObjectNode [] args;
	/**
	 * The kind of event that triggers the callback.
	 */
	final private CallbackNode.Event event;
	
	/**
	 * A dummy context with no arguments.
	 */
	static final private Context defaultContext = new Context(CallbackNode.Event.UNDEFINED, new ObjectNode [0]);
	
	/**
	 * Create a new context. This constructor is kept private 
	 * @see #buildContext(DisplayableNode, navmid.graph.CallbackNode.Event) 
	 * @param e the event that triggers the callback
	 * @param a the arguments given to the callback
	 */
	private Context (CallbackNode.Event e, ObjectNode [] a) { args = a; event = e; }
	
	/**
	 * Access the i-eth argument of the callback
	 * @param i the index
	 * @return the argument returned
	 */
	public ObjectNode get(int i) { return args[i]; }
	
	/**
	 * Adds information to a transition node (done in this context) 
	 * that describes the context of the transition. It is usually the command and sometimes the
	 * item that triggered the transition.
	 * @param tn
	 */
	public void complete(TransitionNode tn) {
		switch(event) {
		case COMMAND :
			tn.linkTo(args[1]);
			break;
		case ITEM:
			tn.linkTo(args[0]);
			tn.linkTo(args[1]);
			break;
		case ITEM_STATE: 
			tn.linkTo(args[0]);
			break;
		}
	}
	
	/**
	 * Depending on the kind of events we are considering and the starting displayable node, builds
	 * the list of contexts that can be used with the callback corresponding to that event.
	 * @param dn the starting displayable
	 * @param e the kind of events considered
	 * @return a list of contexts.
	 */
	static List<Context> buildContext(DisplayableNode dn, CallbackNode.Event e) {
		List <Context> ctxt = new ArrayList<Context> ();
		switch (e) {
		case COMMAND :
			for (Node com : dn.dests(Kind.COMMAND)) {
				ctxt.add(new Context(e, new ObjectNode [] {dn,(CommandNode) com}));
			}
			break;
		case ITEM :
			for (Node item : dn.dests(Kind.ITEM)) {
				for (Node com: item.dests(Kind.COMMAND)) {
					ctxt.add(new Context(e, new ObjectNode [] {(ItemNode) item,(CommandNode) com}));
				}
			}
			break;
		case ITEM_STATE :
			for (Node item : dn.dests(Kind.ITEM)) {
				ctxt.add(new Context(e, new ObjectNode [] {(ItemNode) item}));
			}
			break;
		default :
			ctxt.add(defaultContext);
		}
		return ctxt;
	}
	
	/**
	 * Checks if a context is compatible with a list of nodes. Those nodes should be TestNode
	 * extracted from a path.
	 * @param ltn list of TestNodes
	 * @return true if the context is compatible. false otherwise. In that case the path 
	 * may be pruned.
	 */
	boolean isCompatible(List <Node> ltn) {
		for(Node tn_raw : ltn) {
			if(tn_raw instanceof TestNode) {
				TestNode tn = (TestNode) tn_raw;
				if(! tn.ok(args[tn.position()])) return false;
			}
		}
		return true;
	}
}
