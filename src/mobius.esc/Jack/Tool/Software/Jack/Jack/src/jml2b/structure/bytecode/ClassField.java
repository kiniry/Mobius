/*
 * Created on Apr 20, 2005
 *
 * To change the template for this generated file go to
 * Window&gt;Preferences&gt;Java&gt;Code Generation&gt;Code and Comments
 */
package jml2b.structure.bytecode;

import java.io.Serializable;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.link.LinkContext;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.JmlFile;
import jml2b.structure.java.JmlLoader;
import jml2b.structure.java.Type;
import jml2b.structure.statement.Expression;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.generic.ArrayType;
import org.apache.bcel.generic.ObjectType;

import antlr.collections.AST;

/**
 *
 *  @author L. Burdy
 **/
public class ClassField extends AField implements IModifiers, Serializable {


	transient Field f;
	Type t;
	String fName;
	ClassFile definingClass;
	private boolean fIsProtected;
	private boolean fIsPublic;
	private boolean fIsFinal;
	private boolean fIsPrivate;
	private boolean fIsStatic;
	
	public ClassField(Field field, ClassFile c) {
		f = field;
		definingClass = c;
	}

	/**
	 * @param config
	 */
	public void parse(IJml2bConfiguration config) throws Jml2bException {
		t = getType(config, f.getType());
		fName = f.getName();
		fIsProtected = f.isProtected();
		fIsPublic = f.isPublic();
		fIsFinal = f.isFinal();
		fIsPrivate = f.isPrivate();
		fIsStatic = f.isStatic();
		}

	/**
	 * @param config
	 */
	public static Type getType(IJml2bConfiguration config, org.apache.bcel.generic.Type t) throws Jml2bException {
		if (t == org.apache.bcel.generic.Type.BOOLEAN)
			return   Type.getBoolean();
				else if (t == org.apache.bcel.generic.Type.BYTE) return Type.getByte();
				else if (t == org.apache.bcel.generic.Type.CHAR) return Type.getChar();
				else if (t == org.apache.bcel.generic.Type.INT) return Type.getInteger();
				else if (t == org.apache.bcel.generic.Type.SHORT ) return Type.getShort();
				else if (t == org.apache.bcel.generic.Type.VOID) return  new Type(Type.T_VOID);
				else if (t == org.apache.bcel.generic.Type.FLOAT) return  new Type(Type.T_FLOAT);
				else if (t == org.apache.bcel.generic.Type.DOUBLE) return  new Type(Type.T_DOUBLE);
				else if (t == org.apache.bcel.generic.Type.LONG) return  new Type(Type.T_LONG);
	
	else if (t instanceof ObjectType) {
		return new Type(JmlLoader.loadClass(config, ((ObjectType) t).getClassName()));
	}
	else if (t instanceof ArrayType) {
		return new Type(getType(config, ((ArrayType) t).getElementType()));
	}
	return null;
		}

	public AST parse(JmlFile jmlFile, AST ast) throws Jml2bException {
		return null;
	}

	public void link(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		}
	
	public int linkStatements(IJml2bConfiguration config, LinkContext f) throws Jml2bException {
		return 0;
	}
	public String getName() {
		return fName;
	}

	public Type getType() {
		return t;
	}

	public boolean isExpanded() {
		return false;
	}
	
	public boolean isPure() {
		return false;
	}

	public boolean isLocal() {
		return false;
	}

	public Expression getAssign() {
		return null;
	}

	public AClass getDefiningClass() {
		return definingClass;
	}

	public IModifiers getModifiers() {
		return this;
	}
	
	public boolean isProtectedNotSpecPublic() {
		return fIsProtected;
	}
	public String emit() {
		return "";
	}
	public boolean isExternalVisible() {
		return fIsPublic || fIsProtected;
	}
	public boolean isFinal() {
		return fIsFinal;
	}
	public boolean isPackageVisible() {
		return !fIsPrivate;
	}
	public boolean isPrivate() {
		return fIsPrivate;
	}
	public boolean isProtected() {
		return fIsProtected;
	}
	public boolean isStatic() {
		return fIsStatic;
	}
	
	public boolean isModel() {
		return false;
	}
	public boolean isNative() {
		return false;
	}
	static final long serialVersionUID = 5738853835469755137L;

	public boolean isGhost() {
		return false;
	}

	public boolean isJml() {
		return true;
	}

	public boolean isPublic() {
		return fIsPublic;
	}

}
