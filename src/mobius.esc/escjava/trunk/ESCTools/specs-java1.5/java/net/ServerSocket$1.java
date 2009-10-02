package java.net;

import java.security.PrivilegedExceptionAction;

class ServerSocket$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final ServerSocket this$0;
    
    ServerSocket$1(/*synthetic*/ final ServerSocket this$0) throws NoSuchMethodException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws NoSuchMethodException {
        Class[] cl = new Class[2];
        cl[0] = SocketAddress.class;
        cl[1] = Integer.TYPE;
        ServerSocket.access$000(this$0).getClass().getDeclaredMethod("connect", cl);
        return null;
    }
}
