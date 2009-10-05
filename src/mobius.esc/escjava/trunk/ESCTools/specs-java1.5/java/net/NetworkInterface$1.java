package java.net;

import java.util.Enumeration;
import java.util.NoSuchElementException;
import sun.security.action.*;

class NetworkInterface$1 implements Enumeration {
    /*synthetic*/ final NetworkInterface[] val$netifs;
    
    NetworkInterface$1(/*synthetic*/ final NetworkInterface[] val$netifs) {
        this.val$netifs = val$netifs;
        
    }
    private int i = 0;
    
    public NetworkInterface nextElement() {
        if (val$netifs != null && i < val$netifs.length) {
            NetworkInterface netif = val$netifs[i++];
            return netif;
        } else {
            throw new NoSuchElementException();
        }
    }
    
    public boolean hasMoreElements() {
        return (val$netifs != null && i < val$netifs.length);
    }
    
    /*synthetic public Object nextElement() {
        return this.nextElement();
    } */
}
