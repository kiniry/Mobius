/*
 * Created on 9 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode;

import bcexpression.javatype.JavaReferenceType;

/**
 * @author io
 * @deprecated
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ExceptionHandleBlock extends Block {
	
	private JavaReferenceType exceptionHandled;

	/**
	 * @param _first
	 * @param _last
	 */
	public ExceptionHandleBlock(BCInstruction _first, BCInstruction _last, JavaReferenceType _excHandled ) {
		super(_first, _last);
		setExceptionHandled(_excHandled);
	}
	
	public JavaReferenceType getExceptionhandled() {
		return exceptionHandled;
	}
	
	/**
	 * @param type
	 */
	private void setExceptionHandled(JavaReferenceType type) {
		exceptionHandled = type;
	}

}
