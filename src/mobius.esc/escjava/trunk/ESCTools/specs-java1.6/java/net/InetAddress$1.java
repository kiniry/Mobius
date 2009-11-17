package java.net;

import sun.security.action.*;
import sun.net.spi.nameservice.*;

class InetAddress$1 implements NameService {
    
    InetAddress$1() throws UnknownHostException {
        
    }
    
    public byte[][] lookupAllHostAddr(String host) throws UnknownHostException {
        return InetAddress.impl.lookupAllHostAddr(host);
    }
    
    public String getHostByAddr(byte[] addr) throws UnknownHostException {
        return InetAddress.impl.getHostByAddr(addr);
    }
}
