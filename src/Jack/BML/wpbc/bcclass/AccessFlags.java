/*
 * Created on Sep 21, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcclass;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class AccessFlags {
		private int accessFlags;
		
		public final static short ACC_PUBLIC       = 0x0001;
		public final static short ACC_PRIVATE      = 0x0002;
		public final static short ACC_PROTECTED    = 0x0004;
		public final static short ACC_STATIC       = 0x0008;
		
		public final static short ACC_FINAL        = 0x0010;
		public final static short ACC_SYNCHRONIZED = 0x0020;
		public final static short ACC_VOLATILE     = 0x0040;
		public final static short ACC_TRANSIENT    = 0x0080;
		
		public final static short ACC_NATIVE       = 0x0100;
		public final static short ACC_INTERFACE    = 0x0200;
		public final static short ACC_ABSTRACT     = 0x0400;
		
		public AccessFlags(int _accessFlags) {
			accessFlags = _accessFlags;
		}
		
		public final boolean isPublic() {
		   return (accessFlags &  ACC_PUBLIC) != 0;
		}
		
		public final boolean isPrivate() {
		   return (accessFlags &  ACC_PRIVATE) != 0;
		}
		
		public final boolean isProtected() {
		return (accessFlags &  ACC_PROTECTED) != 0;
		}
		
		
		public final boolean isStatic() {
			return (accessFlags &  ACC_STATIC) != 0;
		 }
		
		public final boolean isFinal() {
			return (accessFlags &  ACC_FINAL) != 0;
		}
		
		
		public final boolean isSynchronized() {
			return (accessFlags &  ACC_SYNCHRONIZED) != 0;
		}
		
		public final boolean isVolatile() {
			return (accessFlags &  ACC_VOLATILE) != 0;
		}
		
		public final boolean isTransient() {
		    return (accessFlags &  ACC_TRANSIENT) != 0;
		}
		
		public final boolean isNative() {
			return (accessFlags &  ACC_NATIVE) != 0;
		}
		
		public final boolean isInterface() {
			return (accessFlags &  ACC_INTERFACE) != 0;
		}
		
		public final boolean isAbstract() {
		     return (accessFlags &  ACC_ABSTRACT) != 0;
		}
		

			
}
