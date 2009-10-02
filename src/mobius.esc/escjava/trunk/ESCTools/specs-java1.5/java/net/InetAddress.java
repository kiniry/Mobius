package java.net;

import java.util.HashMap;
import java.security.AccessController;
import java.io.ObjectStreamException;
import java.io.IOException;
import sun.security.action.*;
import sun.net.InetAddressCachePolicy;
import sun.net.util.IPAddressUtil;
import sun.net.spi.nameservice.*;

public class InetAddress implements java.io.Serializable {
    
    /*synthetic*/ static NameService access$002(NameService x0) {
        return nameService = x0;
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !InetAddress.class.desiredAssertionStatus();
    static final int IPv4 = 1;
    static final int IPv6 = 2;
    static transient boolean preferIPv6Address = false;
    String hostName;
    int address;
    int family;
    private static NameService nameService = null;
    private transient String canonicalHostName = null;
    private static final long serialVersionUID = 3286316764910316507L;
    static {
        preferIPv6Address = ((Boolean)(Boolean)java.security.AccessController.doPrivileged(new GetBooleanAction("java.net.preferIPv6Addresses"))).booleanValue();
        AccessController.doPrivileged(new LoadLibraryAction("net"));
        init();
    }
    
    InetAddress() {
        
    }
    
    private Object readResolve() throws ObjectStreamException {
        return new Inet4Address(this.hostName, this.address);
    }
    
    public boolean isMulticastAddress() {
        return false;
    }
    
    public boolean isAnyLocalAddress() {
        return false;
    }
    
    public boolean isLoopbackAddress() {
        return false;
    }
    
    public boolean isLinkLocalAddress() {
        return false;
    }
    
    public boolean isSiteLocalAddress() {
        return false;
    }
    
    public boolean isMCGlobal() {
        return false;
    }
    
    public boolean isMCNodeLocal() {
        return false;
    }
    
    public boolean isMCLinkLocal() {
        return false;
    }
    
    public boolean isMCSiteLocal() {
        return false;
    }
    
    public boolean isMCOrgLocal() {
        return false;
    }
    
    public boolean isReachable(int timeout) throws IOException {
        return isReachable(null, 0, timeout);
    }
    
    public boolean isReachable(NetworkInterface netif, int ttl, int timeout) throws IOException {
        if (ttl < 0) throw new IllegalArgumentException("ttl can\'t be negative");
        if (timeout < 0) throw new IllegalArgumentException("timeout can\'t be negative");
        return impl.isReachable(this, timeout, netif, ttl);
    }
    
    public String getHostName() {
        return getHostName(true);
    }
    
    String getHostName(boolean check) {
        if (hostName == null) {
            hostName = InetAddress.getHostFromNameService(this, check);
        }
        return hostName;
    }
    
    public String getCanonicalHostName() {
        if (canonicalHostName == null) {
            canonicalHostName = InetAddress.getHostFromNameService(this, true);
        }
        return canonicalHostName;
    }
    
    private static String getHostFromNameService(InetAddress addr, boolean check) {
        String host;
        try {
            host = nameService.getHostByAddr(addr.getAddress());
            if (check) {
                SecurityManager sec = System.getSecurityManager();
                if (sec != null) {
                    sec.checkConnect(host, -1);
                }
            }
            InetAddress[] arr = InetAddress.getAllByName0(host, check);
            boolean ok = false;
            if (arr != null) {
                for (int i = 0; !ok && i < arr.length; i++) {
                    ok = addr.equals(arr[i]);
                }
            }
            if (!ok) {
                host = addr.getHostAddress();
                return host;
            }
        } catch (SecurityException e) {
            host = addr.getHostAddress();
        } catch (UnknownHostException e) {
            host = addr.getHostAddress();
        }
        return host;
    }
    
    public byte[] getAddress() {
        return null;
    }
    
    public String getHostAddress() {
        return null;
    }
    
    public int hashCode() {
        return -1;
    }
    
    public boolean equals(Object obj) {
        return false;
    }
    
    public String toString() {
        return ((hostName != null) ? hostName : "") + "/" + getHostAddress();
    }
    private static InetAddress$Cache addressCache = new InetAddress$Cache(InetAddressCachePolicy.get());
    private static InetAddress$Cache negativeCache = new InetAddress$Cache(InetAddressCachePolicy.getNegative());
    private static boolean addressCacheInit = false;
    static InetAddress[] unknown_array;
    static InetAddressImpl impl;
    private static HashMap lookupTable = new HashMap();
    {
    }
    {
    }
    
    private static void cacheInitIfNeeded() {
        if (!$assertionsDisabled && !Thread.holdsLock(addressCache)) throw new AssertionError();
        if (addressCacheInit) {
            return;
        }
        unknown_array = new InetAddress[1];
        unknown_array[0] = impl.anyLocalAddress();
        addressCache.put(impl.anyLocalAddress().getHostName(), unknown_array);
        addressCacheInit = true;
    }
    
    private static void cacheAddress(String hostname, Object address, boolean success) {
        hostname = hostname.toLowerCase();
        synchronized (addressCache) {
            cacheInitIfNeeded();
            if (success) {
                addressCache.put(hostname, address);
            } else {
                negativeCache.put(hostname, address);
            }
        }
    }
    
    private static Object getCachedAddress(String hostname) {
        hostname = hostname.toLowerCase();
        synchronized (addressCache) {
            InetAddress$CacheEntry entry;
            cacheInitIfNeeded();
            entry = (InetAddress$CacheEntry)addressCache.get(hostname);
            if (entry == null) {
                entry = (InetAddress$CacheEntry)negativeCache.get(hostname);
            }
            if (entry != null) {
                return entry.address;
            }
        }
        return null;
    }
    static {
        impl = (new InetAddressImplFactory()).create();
        String provider = null;
        ;
        String propPrefix = "sun.net.spi.nameservice.provider.";
        int n = 1;
        while (nameService == null) {
            provider = (String)(String)AccessController.doPrivileged(new GetPropertyAction(propPrefix + n, "default"));
            n++;
            if (provider.equals("default")) {
                nameService = new InetAddress$1();
                break;
            }
            final String providerName = provider;
            try {
                java.security.AccessController.doPrivileged(new InetAddress$2(providerName));
            } catch (java.security.PrivilegedActionException e) {
            }
        }
    }
    
    public static InetAddress getByAddress(String host, byte[] addr) throws UnknownHostException {
        if (host != null && host.length() > 0 && host.charAt(0) == '[') {
            if (host.charAt(host.length() - 1) == ']') {
                host = host.substring(1, host.length() - 1);
            }
        }
        if (addr != null) {
            if (addr.length == Inet4Address.INADDRSZ) {
                return new Inet4Address(host, addr);
            } else if (addr.length == Inet6Address.INADDRSZ) {
                byte[] newAddr = IPAddressUtil.convertFromIPv4MappedAddress(addr);
                if (newAddr != null) {
                    return new Inet4Address(host, newAddr);
                } else {
                    return new Inet6Address(host, addr);
                }
            }
        }
        throw new UnknownHostException("addr is of illegal length");
    }
    
    public static InetAddress getByName(String host) throws UnknownHostException {
        return InetAddress.getAllByName(host)[0];
    }
    
    private static InetAddress getByName(String host, InetAddress reqAddr) throws UnknownHostException {
        return InetAddress.getAllByName(host, reqAddr)[0];
    }
    
    public static InetAddress[] getAllByName(String host) throws UnknownHostException {
        return getAllByName(host, null);
    }
    
    private static InetAddress[] getAllByName(String host, InetAddress reqAddr) throws UnknownHostException {
        if (host == null || host.length() == 0) {
            InetAddress[] ret = new InetAddress[1];
            ret[0] = impl.loopbackAddress();
            return ret;
        }
        boolean ipv6Expected = false;
        if (host.charAt(0) == '[') {
            if (host.length() > 2 && host.charAt(host.length() - 1) == ']') {
                host = host.substring(1, host.length() - 1);
                ipv6Expected = true;
            } else {
                throw new UnknownHostException(host);
            }
        }
        if (Character.digit(host.charAt(0), 16) != -1 || (host.charAt(0) == ':')) {
            byte[] addr = null;
            int numericZone = -1;
            String ifname = null;
            addr = IPAddressUtil.textToNumericFormatV4(host);
            if (addr == null) {
                int pos;
                if ((pos = host.indexOf("%")) != -1) {
                    numericZone = checkNumericZone(host);
                    if (numericZone == -1) {
                        ifname = host.substring(pos + 1);
                    }
                }
                addr = IPAddressUtil.textToNumericFormatV6(host);
            } else if (ipv6Expected) {
                throw new UnknownHostException("[" + host + "]");
            }
            InetAddress[] ret = new InetAddress[1];
            if (addr != null) {
                if (addr.length == Inet4Address.INADDRSZ) {
                    ret[0] = new Inet4Address(null, addr);
                } else {
                    if (ifname != null) {
                        ret[0] = new Inet6Address(null, addr, ifname);
                    } else {
                        ret[0] = new Inet6Address(null, addr, numericZone);
                    }
                }
                return ret;
            }
        } else if (ipv6Expected) {
            throw new UnknownHostException("[" + host + "]");
        }
        return getAllByName0(host, reqAddr, true);
    }
    
    private static int checkNumericZone(String s) throws UnknownHostException {
        int percent = s.indexOf('%');
        int slen = s.length();
        int digit;
        int zone = 0;
        if (percent == -1) {
            return -1;
        }
        for (int i = percent + 1; i < slen; i++) {
            char c = s.charAt(i);
            if (c == ']') {
                if (i == percent + 1) {
                    return -1;
                }
                break;
            }
            if ((digit = Character.digit(c, 10)) < 0) {
                return -1;
            }
            zone = (zone * 10) + digit;
        }
        return zone;
    }
    
    private static InetAddress[] getAllByName0(String host) throws UnknownHostException {
        return getAllByName0(host, true);
    }
    
    static InetAddress[] getAllByName0(String host, boolean check) throws UnknownHostException {
        return getAllByName0(host, null, check);
    }
    
    private static InetAddress[] getAllByName0(String host, InetAddress reqAddr, boolean check) throws UnknownHostException {
        Object obj = null;
        Object objcopy = null;
        if (check) {
            SecurityManager security = System.getSecurityManager();
            if (security != null) {
                security.checkConnect(host, -1);
            }
        }
        obj = getCachedAddress(host);
        if (obj == null) {
            try {
                obj = getAddressFromNameService(host, reqAddr);
            } catch (UnknownHostException uhe) {
                throw new UnknownHostException(host + ": " + uhe.getMessage());
            }
        }
        if (obj == unknown_array) throw new UnknownHostException(host);
        objcopy = ((InetAddress[])(InetAddress[])obj).clone();
        return (InetAddress[])(InetAddress[])objcopy;
    }
    
    private static Object getAddressFromNameService(String host, InetAddress reqAddr) throws UnknownHostException {
        Object obj = null;
        boolean success = false;
        if ((obj = checkLookupTable(host)) == null) {
            try {
                byte[][] byte_array;
                byte_array = nameService.lookupAllHostAddr(host);
                InetAddress[] addr_array = new InetAddress[byte_array.length];
                for (int i = 0; i < byte_array.length; i++) {
                    byte[] addr = byte_array[i];
                    if (addr.length == Inet4Address.INADDRSZ) {
                        addr_array[i] = new Inet4Address(host, addr);
                    } else {
                        addr_array[i] = new Inet6Address(host, addr, -1);
                    }
                }
                obj = addr_array;
                success = true;
            } catch (UnknownHostException uhe) {
                obj = unknown_array;
                success = false;
                throw uhe;
            } finally {
                InetAddress[] addrs = (InetAddress[])(InetAddress[])obj;
                if (reqAddr != null && addrs.length > 1 && !addrs[0].equals(reqAddr)) {
                    int i = 1;
                    for (; i < addrs.length; i++) {
                        if (addrs[i].equals(reqAddr)) {
                            break;
                        }
                    }
                    if (i < addrs.length) {
                        InetAddress tmp;
                        InetAddress tmp2 = reqAddr;
                        for (int j = 0; j < i; j++) {
                            tmp = addrs[j];
                            addrs[j] = tmp2;
                            tmp2 = tmp;
                        }
                        addrs[i] = tmp2;
                    }
                }
                cacheAddress(host, obj, success);
                updateLookupTable(host);
            }
        }
        return obj;
    }
    
    private static Object checkLookupTable(String host) {
        Object obj = null;
        synchronized (lookupTable) {
            if (lookupTable.containsKey(host) == false) {
                lookupTable.put(host, null);
                return obj;
            }
            while (lookupTable.containsKey(host)) {
                try {
                    lookupTable.wait();
                } catch (InterruptedException e) {
                }
            }
        }
        obj = getCachedAddress(host);
        if (obj == null) {
            synchronized (lookupTable) {
                lookupTable.put(host, null);
            }
        }
        return obj;
    }
    
    private static void updateLookupTable(String host) {
        synchronized (lookupTable) {
            lookupTable.remove(host);
            lookupTable.notifyAll();
        }
    }
    
    public static InetAddress getByAddress(byte[] addr) throws UnknownHostException {
        return getByAddress(null, addr);
    }
    
    public static InetAddress getLocalHost() throws UnknownHostException {
        SecurityManager security = System.getSecurityManager();
        try {
            String local = impl.getLocalHostName();
            if (security != null) {
                security.checkConnect(local, -1);
            }
            InetAddress[] localAddrs;
            try {
                localAddrs = (InetAddress[])(InetAddress[])InetAddress.getAddressFromNameService(local, null);
            } catch (UnknownHostException uhe) {
                throw new UnknownHostException(local + ": " + uhe.getMessage());
            }
            return localAddrs[0];
        } catch (java.lang.SecurityException e) {
            return impl.loopbackAddress();
        }
    }
    
    private static native void init();
    
    static InetAddress anyLocalAddress() {
        return impl.anyLocalAddress();
    }
    
    static Object loadImpl(String implName) {
        Object impl;
        String prefix = (String)(String)AccessController.doPrivileged(new GetPropertyAction("impl.prefix", ""));
        impl = null;
        try {
            impl = Class.forName("java.net." + prefix + implName).newInstance();
        } catch (ClassNotFoundException e) {
            System.err.println("Class not found: java.net." + prefix + implName + ":\ncheck impl.prefix property " + "in your properties file.");
        } catch (InstantiationException e) {
            System.err.println("Could not instantiate: java.net." + prefix + implName + ":\ncheck impl.prefix property " + "in your properties file.");
        } catch (IllegalAccessException e) {
            System.err.println("Cannot access class: java.net." + prefix + implName + ":\ncheck impl.prefix property " + "in your properties file.");
        }
        if (impl == null) {
            try {
                impl = Class.forName(implName).newInstance();
            } catch (Exception e) {
                throw new Error("System property impl.prefix incorrect");
            }
        }
        return impl;
    }
}
