//******************************************************************************
/* Copyright (c) 2004, 2005 INRIA. All Rights Reserved.
 /*------------------------------------------------------------------------------
 /* Name: 
 /*
 /* Created on Sep 29, 2004
 /*******************************************************************************
 /* Warnings/Remarks:
 /******************************************************************************/
package bytecode_to_JPO;

import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.Type;
import bytecode_wp.bcclass.BCField;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.constants.BCConstantFieldRef;

/**
 * 
 * @author L. Burdy
 */
public class B2JField extends Field implements IModifiers {

	BCField f;
	//BCConstantFieldRef fcp;
	String name;
	B2JClass defC;
	IJml2bConfiguration config;
	/**
	 * @param field
	 */
//	public B2JField(IJml2bConfiguration config, BCConstantFieldRef fieldR, B2JClass def) {
//		this.config = config;
////		BCClass c = ((JavaClassLoader) config.getPackage()).getClass(fieldR.getConstantClass().getName());
////		BCField[] fa = c.getFields();
////		for (int i = 0; i < fa.length; i++) {
////			if (fa[i].getName().equals(fieldR.getName()))
////			f = fa[i];
////		}
//		//fcp = fieldR;
//		f = fieldR.getBCField(config);
//		name = "FieldRef_" + fieldR.getCPIndex() + "_" + fieldR.getName();
//		defC = def;
//	}
	public B2JField(IJml2bConfiguration config, BCField f, B2JClass def) {
		this.config = config;
//		BCClass c = ((JavaClassLoader) config.getPackage()).getClass(fieldR.getConstantClass().getName());
//		BCField[] fa = c.getFields();
//		for (int i = 0; i < fa.length; i++) {
//			if (fa[i].getName().equals(fieldR.getName()))
//			f = fa[i];
//		}
		//fcp = fieldR;
		this.f = f;
//		f = fieldR.getBCField(config);
		name = "FieldRef_" + def.getBName() + "_" + f.getName();
		defC = def;
	}
	public BCField getBCField() {
		return f;
	}

	public String getBName() {
		return name;
	}

	public String getName() {
		return name;
	}
	/**
	 * this method is called when searching for the field corresponding to a cp field index 
	 * called in B2JClass.search(BCConstantFieldRef fieldR)
	 * @return the name of the field
	 */
	public String getBCName() {
		return f.getName();
		//return fcp.getName();
	}
	public boolean isExpanded() {
		return false;
	}
	public JavaType getBCType() {
		return f.getType();
		//return (JavaType)fcp.getType();
	}

	public Type getType() {
		try {
		return B2JProofs.toType(config, f.getType());
		}
		catch (Jml2bException j2be) 
		{
			System.err.println(j2be.getMessage());
			return null;
			}
		}

	public boolean isFinal() {
		return f.isFinal();
	}

	public boolean isPackageVisible() {
		return f.isVisible();
	}

	public boolean isPrivate() {
		return f.isPrivate();
	}

	public boolean isProtected() {
		return f.isProtected();
	}

	public boolean isStatic() {
		return f.isStatic();
	}

	public IModifiers getModifiers() {
		return this;
	}

	public AClass getDefiningClass() {
		return defC;
	}
	
	public boolean isModel() {
		return false;
	}
	
	public boolean isExternalVisible() {
		return f.isPublic() || f.isProtected();
	}
	public boolean isProtectedNotSpecPublic() {
	return f.isProtected();
	}

	public static AField search(IJml2bConfiguration config, BCConstantFieldRef fieldR) {
		B2JClass c = ((B2JPackage) config.getPackage()).search(fieldR.getConstantClass().getName());
		
		if (c == null) {
			c = ((B2JPackage) config.getPackage()).addB2JClass( config, fieldR.getConstantClass().getName(), true);
			
		}
		
		AField af =null;
		
		while (af == null) {
			af = c.search(fieldR);
			c = (B2JClass) c.getSuperClass();
		}
//		if (af == null) {
//			System.out.println(" HERE");
//			af =c.search(fieldR);
//		}
		return af;
//		f = fieldR.getBCField(config);
//		name = "FieldRef_" + fieldR.getCPIndex() + "_" + fieldR.getName();
//		defC = new B2JClass(config, c, false);
	}

	/* (non-Javadoc)
	 * @see jml2b.structure.java.IModifiers#isPure()
	 */
	public boolean isPure() {
	return false;
	}

	public String toString() {
		return name;
	}
	public boolean isGhost() {
		return false;
	}
	public boolean isNative() {
		// TODO Auto-generated method stub
		return false;
	}
}