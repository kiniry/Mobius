/*
 * Created on Apr 20, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure;

import java.util.Enumeration;
import java.util.Vector;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.formula.IModifiesField;
import jml2b.structure.java.Class;
import jml2b.structure.java.Declaration;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.Modifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;
import antlr.collections.AST;

/**
 *
 *  @author L. Burdy
 **/
public abstract class AMethod extends Declaration implements IModifiesField {

	public AMethod() {
	}
	
	public AMethod(JmlFile jf, AST tree, Modifiers m, Class defining)
	throws Jml2bException {
	super(jf, tree, m, defining);
	}
	
	public AMethod(ParsedItem pi, Modifiers m, Class defining)
	throws Jml2bException {
	super(pi, m, defining);
	}
	
	public abstract boolean isStatic();
	/**
	 * @return
	 */
	public abstract String getName() ;
	
	public abstract String getSignature();
	
	public abstract IAParameters getParams();
	
	public abstract boolean isConstructor();
	
	public abstract Type getReturnType();
	
	public String getNameForModifies() {
		return "after " + getName() + getSignature() + " call";
	}
	public abstract Enumeration getSpecCases(IJml2bConfiguration config)
	throws Jml2bException, PogException;
	
	public abstract Expression getNormalizedRequires(IJml2bConfiguration config)
	throws Jml2bException, PogException;
	
	public abstract Expression getNormalizedEnsures(IJml2bConfiguration config)
	throws Jml2bException, PogException;

	public abstract boolean exactMatch(IJml2bConfiguration config, Vector param_types);
	/**
	 * @return
	 */
	public abstract Expression getRequires() ;
	
	public abstract Vector getClonedSpecCases(ParsedItem pi);

}
