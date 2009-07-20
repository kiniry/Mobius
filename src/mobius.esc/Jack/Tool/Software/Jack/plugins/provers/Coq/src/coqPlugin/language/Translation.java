/*
 * Created on Mar 22, 2005
 *
 */
package coqPlugin.language;


/**
 * @author jcharles
 *
 */
public class Translation {
	protected String localDecl = "";
	protected String funPart = "";
	protected CoqType t = new CoqType();
	protected boolean bIsVariableDecl = false;
	private String propPart = "";
	
	public void clearPropPart(){
		propPart = "";
	}
	
	public void addPropPart(Translation prop) {
		addPropPart(prop.propPart);
	}
	public void addPropPart(String prop) {
		if(!propPart.equals("") && !prop.equals("")) {
			//TODO Verifier l'ordre!!! -> je crois que c bon
			propPart = propPart + " -> " + prop;
		}
		else {
			propPart = prop + propPart;
		}
	}
	/**
	 * @return
	 */
	public boolean isVariableDecl() {
		return bIsVariableDecl;
	}
	
	/**
	 * @return
	 */
	public String getPropPart() {
		return propPart;
	}
	
	private String toUniq() {
		if(propPart.equals(""))
			return funPart;
		return propPart + " -> " + funPart;
	}
	
	public String toString() {
		String res = toUniq();
		if(isVariableDecl()){
			return getLocalDecl();
		}
		if (res.equals(""))
			return "True"; 
		return res;
	}
	public String getLocalDecl() {
		if (localDecl == null)
			return "";
		return localDecl.trim();
	}
	public void addLocalDecl(String var, CoqType name) {
		
	}
	
	/**
	 *
	 * @param t
	 */
	public void addLocalDecl(Translation t) {
		if(localDecl.equals("")) {
			localDecl = t.localDecl;
		}
		else { 
			localDecl += " " + t.localDecl;
		}
	}
}
