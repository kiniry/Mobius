package java.net;

import sun.security.action.*;
import sun.net.spi.nameservice.*;

class InetAddressImplFactory {
    
    InetAddressImplFactory() {
        
    }
    
    static InetAddressImpl create() {
        Object o;
        if (isIPv6Supported()) {
            o = InetAddress.loadImpl("Inet6AddressImpl");
        } else {
            o = InetAddress.loadImpl("Inet4AddressImpl");
        }
        return (InetAddressImpl)(InetAddressImpl)o;
    }
    
    static native boolean isIPv6Supported();
}
