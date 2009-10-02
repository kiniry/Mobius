package java.net;

import java.util.Iterator;
import sun.security.action.*;
import sun.misc.Service;
import sun.net.spi.nameservice.*;

class InetAddress$2 implements java.security.PrivilegedExceptionAction {
    /*synthetic*/ final String val$providerName;
    
    InetAddress$2(/*synthetic*/ final String val$providerName) {
        this.val$providerName = val$providerName;
        
    }
    
    public Object run() {
        Iterator itr = Service.providers(NameServiceDescriptor.class);
        while (itr.hasNext()) {
            NameServiceDescriptor nsd = (NameServiceDescriptor)(NameServiceDescriptor)itr.next();
            if (val$providerName.equalsIgnoreCase(nsd.getType() + "," + nsd.getProviderName())) {
                try {
                    InetAddress.access$002(nsd.createNameService());
                    break;
                } catch (Exception e) {
                    e.printStackTrace();
                    System.err.println("Cannot create name service:" + val$providerName + ": " + e);
                }
            }
        }
        return null;
    }
}
