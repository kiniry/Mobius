package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

public class minRegEx {
	minRegEx() {
		exp = "";
		groups = new LinkedHashMap<String, Integer>();
		numberOfGroups = 0;
	}

	minRegEx(String s, LinkedHashMap<String, Integer> m, int num) {
		exp = s;
		groups = m;
		numberOfGroups = num;
	}

	String exp;
	LinkedHashMap<String, Integer> groups;
	int numberOfGroups;

	public String getExp() {
		return exp;
	}

	public void addMiniReg(minRegEx m) {
		// gets linkedhashmap of groups from m
		LinkedHashMap<String, Integer> toLookThrough = m.getGroups();

		// iterate through groups from m and add them to this minRegEx
		int counter = 0;
		Iterator it = toLookThrough.entrySet().iterator();
		while (it.hasNext()) {
			Map.Entry pairs = (Map.Entry) it.next();
			int i = (Integer) pairs.getValue();
			pairs.setValue(numberOfGroups + i);
			counter++;
		}
		numberOfGroups += counter;
		exp = exp.concat(m.getExp());

	}

	public void addMiniReg(minRegEx m, String options) {
		// gets linkedhashmap of groups from m
		LinkedHashMap<String, Integer> toLookThrough = m.getGroups();

		// iterate through groups from m and add them to this minRegEx
		int counter = 0;
		Iterator it = toLookThrough.entrySet().iterator();

		if (options.equals("choice")) {
			while (it.hasNext()) {
				Map.Entry pairs = (Map.Entry) it.next();
				int i = (Integer) pairs.getValue();
				pairs.setValue(numberOfGroups + i);
				counter++;
			}
			numberOfGroups += counter;
			String toReturn=m.getExp();
			exp = exp.concat((toReturn)+"|");

		}
		if (options.equals("optional")) {
			while (it.hasNext()) {
				Map.Entry pairs = (Map.Entry) it.next();
				int i = (Integer) pairs.getValue();
				pairs.setValue(numberOfGroups + i);
				counter++;
			}
			numberOfGroups += counter;
			exp = exp.concat("(?:"+m.getExp()+")");

		}

		
	}

	public LinkedHashMap<String, Integer> getGroups() {
		return groups;
	}

	public void setGroups(LinkedHashMap<String, Integer> groups) {
		this.groups = groups;
	}

	public void setExp(String exp) {
		this.exp = exp;
	}

}
