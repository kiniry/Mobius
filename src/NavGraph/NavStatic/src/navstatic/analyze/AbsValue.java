package navstatic.analyze;

import java.util.ArrayList;
import java.util.List;

public class AbsValue {
	public static class AbsObject extends AbsValue {
		public final int id;
		AbsObject(int id) { this.id = id; }
		public String toString() { return "<refnode id=\"" + id + "\"/>"; }
	}

	public static class AbsString extends AbsValue {
		public final String value;
		AbsString(String value) { this.value = value; }
		public String toString() { return "<string value=\"" + Explorer.htmlProtect(value) + "\"/>"; }
	}

	public static class AbsUnknown extends AbsValue {
		public final String def;
		AbsUnknown(String value) { this.def = value; }
		public String toString() { return "<unknown def=\"" + Explorer.htmlProtect(def) + "\"/>"; }
	}

	public static class AbsInteger extends AbsValue {
		public final int value;
		AbsInteger(int value) { this.value = value; }
		public String toString() { return "<integer value=\"" + value + "\"/>"; }
	}

	public static class AbsParam extends AbsValue {
		public final int position;
		AbsParam(int pos) { this.position = pos; }
		public String toString() { return "<parameter pos=\"" + position + "\"/>"; }
	}

	public static class AbsDisjunct extends AbsValue {
		public final List<AbsValue> contents;
		AbsDisjunct() {	contents = new ArrayList<AbsValue>(); }
		
		AbsDisjunct(List <AbsValue> contents) { this.contents = contents; }
		
		public void add(AbsValue v) { contents.add(v); }
		
		public String toString() {
			StringBuilder buf = new StringBuilder();
			boolean wrapNeeded = contents.size() > 1;
			if (wrapNeeded) buf.append("<or>");
			for(AbsValue n: contents) buf.append(n);
			if (wrapNeeded) buf.append("</or>");
			return buf.toString();
		}
	}
	
	static AbsValue makeDisj(List <AbsValue> l) {
		if (l.size() == 1) { return l.get(0); }
		else return new AbsDisjunct(l);
	}
}
