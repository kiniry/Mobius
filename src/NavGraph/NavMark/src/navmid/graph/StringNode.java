package navmid.graph;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import javax.annotation.Nonnull;

public class StringNode extends Node {
	final String key;
	final Set <String> values;
	private StringNode(String key) {
		super(Kind.STRING);
		this.key = key;
		values = new HashSet<String>();
	}
	
	public void add(@Nonnull String s) {values.add(s); }
	public void add(@Nonnull Collection <String> s) {values.addAll(s); }
	
	public static StringNode getAndSet(Node n, String key) {
		List <Node> attrs = n.dests(Kind.STRING);
		for (Node attr_raw : attrs) {
			StringNode attr = (StringNode) attr_raw;
			if (attr.key.equals(key)) return attr;
		}
		StringNode attr = new StringNode(key);
		n.linkTo(attr);
		return attr;
	}
	
	public static StringNode get(Node n, String key) {
		List <Node> attrs = n.dests(Kind.STRING);
		for (Node attr_raw : attrs) {
			StringNode attr = (StringNode) attr_raw;
			if (attr.key.equals(key)) return attr;
		}
		return null;
	}
	
	public String getToolTip() {
		return "<b>" + key + ":</b>" + values;
	}
	public String toString(){
		return key + ":" + values ;
	}
		
	public boolean isInstanceOf(String c) { return c.equals("java.lang.String") || c.equals("java.lang.Object"); }
}
