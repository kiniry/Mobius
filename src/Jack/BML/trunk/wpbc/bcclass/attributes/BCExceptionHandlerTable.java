/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcclass.attributes;
import org.apache.bcel.generic.CodeExceptionGen;

import bcexpression.javatype.ClassNames;
import bcexpression.javatype.JavaObjectType;
import bcexpression.javatype.JavaType;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public class BCExceptionHandlerTable implements BCAttribute {
	private ExceptionHandler[] excHandlers;
	
	public BCExceptionHandlerTable(CodeExceptionGen[] _excH) {
		excHandlers = new ExceptionHandler[_excH.length];
		for (int i = 0; i < _excH.length; i++) {
			JavaObjectType caughtExcType;
			if (_excH[i].getCatchType() == null) {
				caughtExcType = (JavaObjectType)JavaType.getJavaRefType(ClassNames.Exception );
			} else {
				caughtExcType = (JavaObjectType)JavaType.getJavaRefType(_excH[i].getCatchType() );
			}
			excHandlers[i] = new ExceptionHandler(
					_excH[i].getStartPC()
							.getPosition(), 
					_excH[i].getEndPC().getPosition(),
					caughtExcType, 
					_excH[i].getHandlerPC()
							.getPosition());
		}
	}

	
	/**
	 * @return Returns the excHandlers.
	 */
	public ExceptionHandler[] getExcHandlers() {
		return excHandlers;
	}
}
