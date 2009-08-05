package navmid.track;

import java.awt.Color;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import navmid.graph.ActionNode;
import navmid.graph.DisplayableNode;
import navmid.graph.ObjectNode;

public final class Tracker implements Runnable {
	private final SerialConnection serial;
	private String[] components;
	private final TrackerListener listener;
	private HashMap <String, ObjectNode> dynamicToAbstract;
	private ObjectNode current = null;
	private Set <ActionNode> currentActions;

	enum Command {
		Tag,CallCommandListener,CallItemCommandListener,AddCommand,AddCommandListener,SetCurrent,Error;
		public static Command c(String str) {
			try {return valueOf(str);} catch (Exception ex){return Error;} 
		}
		
	}
	public Tracker(SerialConnection sc, TrackerListener tl) {
		dynamicToAbstract = new HashMap <String,ObjectNode> ();
		currentActions = new HashSet<ActionNode>();
		serial = sc;
		listener = tl;
	}
	
	public void track() {
		new Thread(this).start();
	}
	
	private String [] getLine() {
		String line;
		do { line = serial.get(); } while (line != null && line.equals(""));
		
		if (line == null) return null;
		return line.split(":",3);
	}
	
	private Command getCommand() {
		components = getLine();
		if(components == null || components.length != 2 || !components[0].equals("A"))
			return Command.Error;
		return Command.c(components[1]);
	}
	
	private String getArgument() {
		components = getLine();
		if(components == null || components.length != 3 || !components[0].equals("-"))
			return "";
		return components[2];
	}
	
	/**
	 * Called when the current displayable is changed. The previous current node is reset. 
	 * @param node The new node.
	 */
	private void setCurrent(ObjectNode node) {
		if (current != null) {
			current.setColor(null);
			listener.update(current);
		}
		current = node;
		node.setColor(Color.RED);
		listener.update(node);
	}
	
	private void addAction(ActionNode node) {
		currentActions.add(node);
		node.setColor(Color.YELLOW);
		listener.update(node);
	}
	
	private void clearActions() {
		for(ActionNode an: currentActions) {
			an.setColor(null);
			listener.update(an);
		}
		currentActions.clear();
	}
	
	public void run() {
		System.err.println("Tracker started.");
		setCurrent(DisplayableNode.start);
		while(serial.isOpen()) {
			Command command = getCommand();
			switch (command) {
			case Tag: {
				String name =  getArgument();
				String from_spec = getArgument();
				System.err.println("Looking for " + from_spec);
				ObjectNode obj = ObjectNode.getObject(from_spec);
				if(obj==null) continue;
				obj.identify();
				dynamicToAbstract.put(name, obj);
				System.err.println("Tag" + name + " " + obj);
				listener.update(obj);
				break;
			}
			case SetCurrent: {
				String name = getArgument();
				String position = getArgument();
				ActionNode act = ActionNode.getAction(position);
				addAction(act);
				ObjectNode obj = dynamicToAbstract.get(name);
				if (obj != null) setCurrent(obj);
				break;
			}
			case CallCommandListener: {
				String commandListenerId = getArgument();
				ObjectNode commandListener = dynamicToAbstract.get(commandListenerId);
				String commandId = getArgument();
				ObjectNode comm = dynamicToAbstract.get(commandId);
				String screenId = getArgument();
				ObjectNode screen  = dynamicToAbstract.get(screenId);
				clearActions();
				break;
			}
			default:
				// System.err.println("other");
				break;
			}
		}
		System.err.println("Tracker stopped.");
	}

}
