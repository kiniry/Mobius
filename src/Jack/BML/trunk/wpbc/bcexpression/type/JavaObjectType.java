/*
 * Created on Mar 23, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression.type;

import org.apache.bcel.generic.ObjectType;
import org.apache.bcel.generic.Type;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class JavaObjectType extends JavaReferenceType {

	/**
	 * @param _type
	 */
	public JavaObjectType(Type _type) {
		super(_type);
	}
	
	public boolean subclassOf(JavaReferenceType  _ot) {
	   return ((ObjectType)type).subclassOf((ObjectType)_ot.type);
   }

}
