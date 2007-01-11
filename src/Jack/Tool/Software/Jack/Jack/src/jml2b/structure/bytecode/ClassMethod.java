/*
 * Created on Apr 20, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.bytecode;

import java.io.Serializable;
import java.util.Enumeration;
import java.util.Vector;

import org.apache.bcel.classfile.Method;

import antlr.collections.AST;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.exceptions.PogException;
import jml2b.link.LinkContext;
import jml2b.structure.AMethod;
import jml2b.structure.IAParameters;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import jml2b.structure.jml.SpecCase;
import jml2b.structure.statement.Expression;
import jml2b.structure.statement.MyToken;
import jml2b.structure.statement.TerminalExp;

/**
 *
 *  @author L. Burdy
 **/
public class ClassMethod extends AMethod implements IModifiers, Serializable {

	static final long serialVersionUID = -1285093836213862326L;

	transient Method m;
	ClassFile definingClass;
	Type returnType;
	ClassParameters cp;
	String mName;
	String mSignature;
	org.apache.bcel.generic.Type[] mArgumentType;

	private boolean mIsProtected;

	private boolean mIsPublic;

	private boolean mIsFinal;

	private boolean mIsPrivate;

	private boolean mIsStatic;
	
	Vector sc;

	ClassMethod(ClassFile cf) {
		definingClass = cf;
	}
	
	public ClassMethod(Method method, ClassFile cf) {
		m = method;
		definingClass = cf;
	}

	public void parse(IJml2bConfiguration config) throws Jml2bException {
		returnType = ClassField.getType(config, m.getReturnType());
		cp = new ClassParameters(config, m);
		mName  = m.getName();
		mSignature = m.getSignature();
		mIsProtected = m.isProtected();
		mIsPublic = m.isPublic();
		mIsFinal = m.isFinal();
		mIsPrivate = m.isPrivate();
		mIsStatic = m.isStatic();
		mArgumentType = m.getArgumentTypes();
		sc = new Vector();
		LinkContext lc = new LinkContext(definingClass);
		lc.currentMethod = this;
		sc.add(new SpecCase(config, lc));
	}

	public String emit() {
		return "";
	}
	public boolean isExternalVisible() {
			return mIsPublic || mIsProtected;
	}
	public boolean isFinal() {
			return mIsFinal;
	}
	public boolean isPackageVisible() {
		return !mIsPrivate;
	}
	public boolean isPrivate() {
		return mIsPrivate;
	}
	public boolean isProtected() {
		return mIsProtected;
	}
	public boolean isProtectedNotSpecPublic() {
		return mIsProtected;
	}
	public boolean isStatic() {
		return mIsStatic;
	}

	public boolean isModel() {
		return false;
	}	
	public boolean isNative() {
		return false;
	}
	/**
	 * @param param_types
	 * @param argumentTypes
	 * @return
	 */
	public boolean exactMatch(IJml2bConfiguration config, Vector param_types) {
		if (param_types.size() == mArgumentType.length) {
			int i=0;
			Enumeration e = param_types.elements();
			while (e.hasMoreElements()) {
				Type t = (Type) e.nextElement();
				if (!ClassFile.matchingType(config, t, mArgumentType[i++]))
					return false;
			}
			return true;
		}
		return false;
	}

	public boolean matchingSignaturesF(IJml2bConfiguration config, Vector field_types) {
		if (field_types.size() == mArgumentType.length) {
			int i=0;
			Enumeration e = field_types.elements();
			while (e.hasMoreElements()) {
				Field t = (Field) e.nextElement();
				if (!ClassFile.matchingType(config, t.getType(), mArgumentType[i++]))
					return false;
			}
			return true;
		}
		return false;
	}

//	public boolean isCompatible(Vector param_types) {
//		return false;
//	}
//

	public String getName() {
		return mName;
	}

	public String getSignature() {
		return mSignature;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.AMethod#getSign()
	 */
	public IAParameters getParams() {
		return cp;
	}

	public String getInfo() {
		return "";
	}

	public String getInfo(String ret) {
		return "";
	}

	public boolean isConstructor() {
		return mName.equals(definingClass.getName());
	}

	public Type getReturnType() {
		return returnType;
	}

	public Enumeration getSpecCases(IJml2bConfiguration config) throws Jml2bException, PogException {
		return sc.elements();
	}

	public Expression getNormalizedRequires(IJml2bConfiguration config) throws Jml2bException, PogException {
		return new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	public Expression getNormalizedEnsures(IJml2bConfiguration config) throws Jml2bException, PogException {
		return new TerminalExp(MyToken.BTRUE, "(0=0)");
	}

	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		return null;
	}

	public void link(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
	}

	public int linkStatements(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return 0;
	}

	public Vector getClonedSpecCases(ParsedItem pi) {
		return new Vector();
	}
	public Expression getRequires() {
		return null;
	}

	/**
	 * @return
	 */
	public boolean isDefaultConstructor(String name) {
		return getName().equals(name) && mArgumentType.length == 0;
	}
	public AClass getDefiningClass() {
		return definingClass;
	}

	public IModifiers getModifiers() {
		return this;
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.java.IModifiers#isPure()
	 */
	public boolean isPure() {
		return false;
	}

	public boolean isGhost() {
		return false;
	}

	public boolean isJml() {
		return true;
	}

	public boolean isPublic() {
		return mIsPublic;
	}

}
