package java.util.zip;

import java.security.PrivilegedAction;
import java.lang.reflect.*;

class ZipFile$1 implements PrivilegedAction {
    
    ZipFile$1() {
        
    }
    
    public Object run() {
        try {
            Class th = Class.forName("java.nio.DirectByteBuffer");
            ZipFile.access$102(th.getDeclaredConstructor(new Class[]{Integer.TYPE, Long.TYPE, Runnable.class}));
            ZipFile.access$100().setAccessible(true);
        } catch (ClassNotFoundException x) {
            throw new InternalError();
        } catch (NoSuchMethodException x) {
            throw new InternalError();
        } catch (IllegalArgumentException x) {
            throw new InternalError();
        } catch (ClassCastException x) {
            throw new InternalError();
        }
        return null;
    }
}
