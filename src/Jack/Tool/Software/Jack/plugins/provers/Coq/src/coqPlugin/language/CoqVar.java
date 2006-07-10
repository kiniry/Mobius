/*
 * Created on Mar 21, 2005
 */
package coqPlugin.language;

import java.util.ArrayList;

import jml2b.exceptions.LanguageException;
import jml2b.formula.Formula;
import jml2b.formula.IFormToken;
import jpov.structure.Lemma;

/**
 * @author jcharles
 *
 */
public class CoqVar {
	private static ArrayList nameTable = new ArrayList();
	private static ArrayList translationTable = new ArrayList();
	public final static CoqVar vide = new CoqVar();
	
	public static boolean putName(String jackName) {
		if(nameTable.indexOf(jackName) == -1) {
			nameTable.add(jackName);
			if(jackName.startsWith("l_")) {
				int i= jackName.length() -1;
				for(; (i>0) && 
					(jackName.charAt(i) >= '0') && (jackName.charAt(i) <= '9');
					i--);
				String shortName = prefix + jackName.substring(0, i +1);
				if(translationTable.indexOf(shortName) != -1) { 
					int count = 0;
					while (translationTable.indexOf(shortName + count) != -1) {
						count++;
					}
					shortName = shortName + count;
				}
				translationTable.add(shortName);
			}
			else {
				translationTable.add(jackName );
			}
			return true;
		}
		return false;
	}
	public static void putStupidName(String jackName) {
		String [] tab = jackName.split("_");
		if(tab.length != 3) {
			putName(jackName);
			return;
		}
		if(!putName(tab[0] + "_" + tab[1]))
			return;
		int index = nameTable.size() -1;
		nameTable.set(index, jackName);
		translationTable.set(index, translationTable.get(index) + "_" +tab[2]);
		
	}
	private static String prefix = "";
	public static void setPrefix(Lemma l) {
//		prefix = "";
		if(l == null) {
			prefix = "";
			return;
		}		
		
		String beg = l.getName().replace('_', '.');
		if(beg.length() > 2) {
			beg.substring(2);
		}
		else {
			beg = "method_" + beg;
		}
		beg.replaceAll("method\\.", "method_");
		prefix = beg + "-" + l.getNum();
	}
	public static String getCoqName(String jackName) {
		int index = 0;
		if((index = nameTable.indexOf(jackName)) == -1) {
			index = nameTable.indexOf(prefix + 
					jackName);

			return translationTable.get(index).toString().substring(0, prefix.length());
		}
		else {
			return translationTable.get(index).toString();
		}
	}
	
	
	private final String name;
	private final CoqType type;
	private final CoqVar next;
	
	public CoqVar() {
		this(null);
	}
	
	public CoqVar(CoqVar next) {
		this(next, null);
	}
	
	
	public CoqVar(CoqVar next, String name) {
		this(next, name, null);
	}
	
	
	public CoqVar(CoqVar next, String name, CoqType type) {
		this.next = next;
		this.name = name;
		this.type = type;
	}
	
	public CoqVar(String name, Formula type) throws LanguageException {
		this.name = name;
		if(isMemberField(name, type)) {
			String typeName = name.substring(0, name.lastIndexOf("_")+1) + "type";
			this.type = new CoqType(typeName);
		} else if (name.startsWith("arraylength")) {
			this.type = CoqType.arraylength;
		} else {
			this.type = CoqType.getType(type);
		}
		next = vide;
	}
	public static boolean isMemberField(Formula cbf) {
		int type = cbf.getNodeType();
		return (type == IFormToken.IS_MEMBER_FIELD);
	}
	public static boolean isMemberField(String name, Formula cbf) {
		int type = cbf.getNodeType();
		return isMemberField(cbf) || ((type == IFormToken.IS_ARRAY) && name.startsWith("f_")) ||
					name.startsWith("f_");
	}
	public String toString() {
		if(name == null) 
			return "";
		else if (type == null) 
			return name + " " + next;
		else
			return "(" + name + ": " + type + ") " + next;
		
	}
	
	
}
