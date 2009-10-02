package java.net;

import java.security.PrivilegedAction;

class Socket$1 implements PrivilegedAction {
    /*synthetic*/ final Socket this$0;
    
    Socket$1(/*synthetic*/ final Socket this$0) {
        this.this$0 = this$0;
        
    }
    
    public Boolean run() {
        Class[] cl = new Class[2];
        cl[0] = SocketAddress.class;
        cl[1] = Integer.TYPE;
        Class clazz = this$0.impl.getClass();
        while (true) {
            try {
                clazz.getDeclaredMethod("connect", cl);
                return Boolean.FALSE;
            } catch (NoSuchMethodException e) {
                clazz = clazz.getSuperclass();
                if (clazz.equals(SocketImpl.class)) {
                    return Boolean.TRUE;
                }
            }
        }
    }
    
    /*synthetic*/ public Object run() {
        return this.run();
    }
}
