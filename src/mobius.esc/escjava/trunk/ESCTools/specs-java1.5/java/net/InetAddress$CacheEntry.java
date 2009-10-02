package java.net;

import sun.security.action.*;
import sun.net.spi.nameservice.*;

final class InetAddress$CacheEntry {
    
    InetAddress$CacheEntry(Object address, long expiration) {
        
        this.address = address;
        this.expiration = expiration;
    }
    Object address;
    long expiration;
}
