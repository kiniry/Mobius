package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.regex.*;

public class Property {

	// definition of exceptable properties using regular expressions

	final static String prop_Scope = "(files|modules|features|variables|all|special)";
	final static String prop_Description = ".*";
	final static String prop_format = "(.*|[(.*,)*.*]|optional:.*)";
	final static String prop_Name = "\\w+";

	// class variables
	public static ArrayList<Object> format;
	public static ArrayList<String> scope;
	public static String description;
	public static String name;

	public Property() {
		format = new ArrayList<Object>();
		scope = new ArrayList<String>();
		description = new String();
		name = new String();

	}

	public boolean checkValidity() {
		Pattern scopePattern = Pattern.compile(prop_Scope,
				Pattern.CASE_INSENSITIVE);
		Pattern descriptionPattern = Pattern.compile(prop_Description,
				Pattern.DOTALL);
		Pattern namePattern = Pattern.compile(prop_Name);

		// check name
		Matcher nameMatcher = namePattern.matcher(name);
		if (!nameMatcher.matches()) {
			System.out.println(" name value is invalid @" + name);
		}

		// check scopes
		for (String scopeValue : scope) {
			Matcher scopeMatcher = scopePattern.matcher(scopeValue);
			if (!scopeMatcher.matches()) {
				System.out.println(name + " scope value is invalid @"
						+ scopeValue);
				return false;
			}
		}

		// check Description
		Matcher descriptionMatcher = descriptionPattern.matcher(description);
		if (!descriptionMatcher.matches()) {
			System.out.println("The  properties description is invalid @"
					+ description);
			return false;
		}

		// check format
		return checkFormatValidity(format);

	}

	private boolean checkFormatValidity(Object nameValue) {

		Pattern formatPattern = Pattern.compile(prop_format);
		// case for normal property
		if (nameValue instanceof String) {
			Matcher nameMatcher = formatPattern.matcher((String) nameValue);
			if (!nameMatcher.matches()) {
				System.out.println(" name value is invalid @" + nameValue);
				return false;
			}
		}
		// case for inner list [a,b,c]
		else if (nameValue instanceof ArrayList<?>) {
			for (Object optionalNameValue : (ArrayList<?>) nameValue) {
				checkFormatValidity(optionalNameValue);

			}

		}
		// case for optional: or choice: -- needs more complete implementation
		// to avoid false positives
		else if (nameValue instanceof LinkedHashMap<?, ?>) {
			LinkedHashMap<String, ?> r = (LinkedHashMap<String, ?>) nameValue;

			if (r.containsKey("choice")) {
				checkFormatValidity(r.get("choice"));
			}
			if (r.containsKey("optional")) {
				checkFormatValidity(r.get("optional"));
			}
		}

		else if (nameValue instanceof MyObject) {

		}
		// any case i didn't predict
		else {
			System.out
					.println("Should not have got here in name check, reason @ "
							+ nameValue);
		}
		return true;

	}

	public static minRegEx generateRegExp() {
		minRegEx returnRegEx = new minRegEx();
		returnRegEx.addMiniReg(generateRegExp(format, "normal"),"normal");
		return returnRegEx;
	}

	public static minRegEx generateRegExp(Object ob, String options) {

		// optional: case
		if (options.equals("optional")) {
			minRegEx returner = new minRegEx();
			returner.addMiniReg(generateRegExp(ob, "normal"), "optional");
			return returner;
		}

		//when arraylist
		if (ob instanceof ArrayList<?>) {

			String list = "\\s+";
			ArrayList<?> l = (ArrayList<?>) ob;
			minRegEx returner = new minRegEx();

			// non capturing choice: case
			if (options.equals("choice")) {
				returner.setExp(returner.getExp().concat("(?:"));
				for (Object obin : l) {
					minRegEx temp = generateRegExp(obin, "normal");
					returner.addMiniReg(temp, "choice");
				}
				String curentRep = returner.getExp();

				returner.setExp((curentRep.substring(0,curentRep.length()-1)).concat(")"));

			}

			// normal case
			else {
				// put in space
				for (Object obin : l) {
					minRegEx temp = generateRegExp(obin, "normal");
					returner.addMiniReg(temp,"normal");
				}
			}
			return returner;

		}
		// if map
		if (ob instanceof LinkedHashMap<?, ?>) {
			minRegEx thisHashMap = new minRegEx();
			// go through all objects in linked hashmap and add their respective
			// regex to this one
			LinkedHashMap<?, ?> all = (LinkedHashMap<?, ?>) ob;
			Iterator it = all.entrySet().iterator();
			while (it.hasNext()) {

				Map.Entry pairs = (Map.Entry) it.next();
				minRegEx temp = new minRegEx();
				if (pairs.getKey() instanceof String) {
					String compar = (String) pairs.getKey();
					if (compar.equals("choice")) {
						temp = generateRegExp(pairs.getValue(), "choice");
					} else if (compar.equals("optional")) {
						temp = generateRegExp(pairs.getValue(), "optional");
					}

				} else {
					temp = generateRegExp(pairs.getValue(), "normal");
				}

				thisHashMap.addMiniReg(temp,"normal");
			}
			// return full expression for this hash map
			return thisHashMap;

		}
		// if string
		if (ob instanceof String) {

			return new minRegEx((String) ob,
					new LinkedHashMap<String, Integer>(), 0);

		}
		// custom objects
		if (ob instanceof MyObject) {
			MyObject thisOb = (MyObject) ob;
			LinkedHashMap<String, Integer> objectMap = new LinkedHashMap<String, Integer>();
			objectMap.put(thisOb.getId(), 1);

			return new minRegEx("(" + thisOb.getReg() + ")", objectMap, 1);

		}
		return new minRegEx(
				"unexpected type encountered when generating RegExp in Propery.class"
						+ ob, new LinkedHashMap<String, Integer>(), 0);

	}

	public static String getName() {
		return name;
	}

	public static void setName(String name) {
		Property.name = name;
	}

	public static ArrayList<String> getScope() {
		return scope;
	}

	public void setScope(ArrayList<String> scope) {
		Property.scope = scope;
	}

	public static String getDescription() {
		return description;
	}

	public void setDescription(String string) {
		Property.description = string;
	}

	public void setFormat(ArrayList<Object> format) {
		Property.format = format;
	}

	public static ArrayList<Object> getFormat() {
		return format;
	}

}
