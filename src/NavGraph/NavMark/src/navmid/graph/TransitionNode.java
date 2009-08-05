package navmid.graph;

import java.util.ArrayList;
import java.util.List;

import navmid.graph.ActionNode.ActionKind;

/**
 * A synthetic transition associated to a displayable. It is defined by its destinations which
 * represent the target display, the commands used and the potential actions.
 * @author piac6784
 *
 */
public class TransitionNode extends Node {
	
	/**
	 * The event that triggered the transition. 
	 */
	final CallbackNode.Event event;
	
	public TransitionNode(CallbackNode.Event e) {
		super(Kind.TRANSITION);
		event = e;
	}
	
	public String toString() {
		List <Node> r = new ArrayList<Node>();
		for(Node x:this.dests(Kind.COMMAND)) r.addAll(x.dests(Kind.STRING));
		return r.toString(); 
	}

	/**
	 * Kind of equality test for transition linked to a given node. They are the same iff their
	 * destinations (labels and actions) are the same. Otherwise it is a new transition and should
	 * be added to the graph.
	 * @param n the node to which we want to add the transition
	 * @return true only if there is no equivalent transition already registered.
	 */
	public boolean newTransition(Node n) {
		for(Node t: n.dests(Kind.TRANSITION)) {
			if(this.dests.containsAll(t.dests) && t.dests.containsAll(this.dests)) return false;
		}
		return true;
	}
	
	/**
	 * Builds synthetic transition on the current graph. This is the core method of the application.
	 * Starting from a graph that records the elementary relations between objects as identified by 
	 * navstatic, it synthesizes the high level transitions between two displayable nodes annotated
	 * with the commands that trigger the transitions and the actions performed on those transitions.
	 */
	static public void buildAll() {
		for(Node startNode_raw: Node.all(Kind.DISPLAYABLE)) {
			DisplayableNode startNode = (DisplayableNode) startNode_raw;
			for(Node lan_raw : startNode.dests(Kind.LISTENER_ASSO)) {
				ListenerAssociationNode lan = (ListenerAssociationNode) lan_raw;
				CallbackNode.Event e = lan.event();
				List <Context> lco = Context.buildContext(startNode, e);
				for(Node list : lan.dests(Kind.LISTENER)) {
					for(Node list_class : list.dests(Kind.LISTENER_CLASS)) {
						for(Node callback_raw : list_class.dests(Kind.CALLBACK)) {
							CallbackNode callback = (CallbackNode) callback_raw;
							if (callback.hasPurpose(e)) {
								for(Node path_raw : callback.dests(Kind.PATH)) {
									PathNode path = (PathNode) path_raw;
									List <Node> ltn = path.dests(Kind.GUARD);
									for(Context co : lco) {
										if(co.isCompatible(ltn)) {
											TransitionNode tn = new TransitionNode(e);
											for(Node a_raw:path.dests(Kind.ACTION)) {
												ActionNode a = (ActionNode) a_raw;
												if (a.kind.equals(ActionKind.SETDISPLAY))
													for(Node d:a.dests(Kind.DISPLAYABLE)) tn.linkTo(d);
												else tn.linkTo(a);
											}
											co.complete(tn);
											if (tn.newTransition(startNode)) startNode.linkTo(tn);
											else tn.delete();
										}
									}
								}
							}
						}
					}
				}
			}
		}
	}
}
