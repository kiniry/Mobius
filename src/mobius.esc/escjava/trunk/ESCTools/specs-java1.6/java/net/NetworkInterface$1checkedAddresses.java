package java.net;

import java.util.Enumeration;
import java.util.NoSuchElementException;
import sun.security.action.*;

class NetworkInterface$1checkedAddresses implements Enumeration {
    /*synthetic*/ final NetworkInterface this$0;
    private int i = 0;
    private int count = 0;
    private InetAddress[] local_addrs;
    
    NetworkInterface$1checkedAddresses(/*synthetic*/ final NetworkInterface this$0) {
        this.this$0 = this$0;
        
        local_addrs = new InetAddress[NetworkInterface.access$000(this$0).length];
        SecurityManager sec = System.getSecurityManager();
        for (int j = 0; j < NetworkInterface.access$000(this$0).length; j++) {
            try {
                if (sec != null) {
                    sec.checkConnect(NetworkInterface.access$000(this$0)[j].getHostAddress(), -1);
                }
                local_addrs[count++] = NetworkInterface.access$000(this$0)[j];
            } catch (SecurityException e) {
            }
        }
    }
    
    public InetAddress nextElement() {
        if (i < count) {
            return local_addrs[i++];
        } else {
            throw new NoSuchElementException();
        }
    }
    
    public boolean hasMoreElements() {
        return (i < count);
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
