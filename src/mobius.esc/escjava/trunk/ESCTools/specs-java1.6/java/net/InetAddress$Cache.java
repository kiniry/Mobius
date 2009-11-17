package java.net;

import java.util.LinkedHashMap;
import java.util.Iterator;
import java.util.LinkedList;
import sun.security.action.*;
import sun.net.InetAddressCachePolicy;
import sun.net.spi.nameservice.*;

final class InetAddress$Cache {
    private int policy;
    private LinkedHashMap cache;
    
    public InetAddress$Cache(int policy) {
        
        this.policy = policy;
        cache = new LinkedHashMap();
    }
    
    public InetAddress$Cache put(String host, Object address) {
        if (policy == InetAddressCachePolicy.NEVER) {
            return this;
        }
        if (policy != InetAddressCachePolicy.FOREVER) {
            LinkedList expired = new LinkedList();
            Iterator i = cache.keySet().iterator();
            long now = System.currentTimeMillis();
            while (i.hasNext()) {
                String key = (String)(String)i.next();
                InetAddress$CacheEntry entry = (InetAddress$CacheEntry)(InetAddress$CacheEntry)cache.get(key);
                if (entry.expiration >= 0 && entry.expiration < now) {
                    expired.add(key);
                } else {
                    break;
                }
            }
            i = expired.iterator();
            while (i.hasNext()) {
                cache.remove(i.next());
            }
        }
        long expiration;
        if (policy == InetAddressCachePolicy.FOREVER) {
            expiration = -1;
        } else {
            expiration = System.currentTimeMillis() + (policy * 1000);
        }
        InetAddress$CacheEntry entry = new InetAddress$CacheEntry(address, expiration);
        cache.put(host, entry);
        return this;
    }
    
    public InetAddress$CacheEntry get(String host) {
        if (policy == InetAddressCachePolicy.NEVER) {
            return null;
        }
        InetAddress$CacheEntry entry = (InetAddress$CacheEntry)(InetAddress$CacheEntry)cache.get(host);
        if (entry != null && policy != InetAddressCachePolicy.FOREVER) {
            if (entry.expiration >= 0 && entry.expiration < System.currentTimeMillis()) {
                cache.remove(host);
                entry = null;
            }
        }
        return entry;
    }
}
