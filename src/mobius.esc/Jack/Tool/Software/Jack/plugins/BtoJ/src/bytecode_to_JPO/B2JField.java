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

import jack.util.Logger;
import jml2b.IJml2bConfiguration;
import jml2b.exceptions.Jml2bException;
import jml2b.pog.util.IdentifierResolver;
import jml2b.structure.AField;
import jml2b.structure.java.AClass;
import jml2b.structure.java.Field;
import jml2b.structure.java.IModifiers;
import jml2b.structure.java.ParsedItem;
import jml2b.structure.java.Type;
import bytecode_wp.bcclass.BCField;
import bytecode_wp.bcexpression.javatype.JavaType;
import bytecode_wp.constants.BCConstantFieldRef;

/**
 * 
 * @author L. Burdy
 */
public class B2JField extends Field {

	/** */
	private static final long serialVersionUID = 1L;
	private BCField f;
	private B2JClass defC;
	/**
	 * @param field
	 */

	
	public B2JField(IJml2bConfiguration config, BCField f, B2JClass def) {
		super(ParsedItem.$empty, getModifiers(f), getType(config, f), 
				f.getName(), null);
		this.f = f;
		defC = def;
		
		nameIndex = IdentifierResolver.addIdent(this);
	}
	private static Type getType(IJml2bConfiguration config, BCField f) {
		try {
			return B2JProofs.toType(config, f.getType());
		}
		catch (Jml2bException j2be) 
		{
				Logger.err.println(j2be.getMessage());
				return null;
		}
	}
	public static class FieldModifier implements IModifiers {
		private BCField f;
		public FieldModifier(BCField f) {
			this.f = f;
		}
		
		public String emit() {
			//TODO: implement it.
			return "";
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
		

		public boolean isExternalVisible() {
			return f.isPublic() || f.isProtected();
		}
		public boolean isProtectedNotSpecPublic() {
		return f.isProtected();
		}
		
		public boolean isPure() {
			return false;
		}
		public boolean isGhost() {
			return false;
		}
		public boolean isNative() {
			return false;
		}
		

		public boolean isModel() {
			return false;
		}

		public boolean isJml() {
			return true;
		}

		public boolean isPublic() {
			return f.isPublic();
		}
		
		
	}
	
	private static IModifiers getModifiers(BCField f) {
		return new FieldModifier(f);
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


	public AClass getDefiningClass() {
		return defC;
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
//			Logger.get().println(" HERE");
//			af =c.search(fieldR);
//		}
		return af;
//		f = fieldR.getBCField(config);
//		name = "FieldRef_" + fieldR.getCPIndex() + "_" + fieldR.getName();
//		defC = new B2JClass(config, c, false);
	}



}