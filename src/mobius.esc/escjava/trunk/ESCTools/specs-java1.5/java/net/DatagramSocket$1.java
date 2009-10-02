package java.net;

import java.security.PrivilegedExceptionAction;

class DatagramSocket$1 implements PrivilegedExceptionAction {
    /*synthetic*/ final DatagramSocket this$0;
    
    DatagramSocket$1(/*synthetic*/ final DatagramSocket this$0) throws NoSuchMethodException {
        this.this$0 = this$0;
        
    }
    
    public Object run() throws NoSuchMethodException {
        Class[] cl = new Class[1];
        cl[0] = DatagramPacket.class;
        this$0.impl.getClass().getDeclaredMethod("peekData", cl);
        return null;
    }
}
