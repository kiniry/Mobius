package java.net;

import java.io.IOException;

class Inet6AddressImpl implements InetAddressImpl {
    
    Inet6AddressImpl() {
        
    }
    
    public native String getLocalHostName() throws UnknownHostException;
    
    public native byte[][] lookupAllHostAddr(String hostname) throws UnknownHostException;
    
    public native String getHostByAddr(byte[] addr) throws UnknownHostException;
    
    private native boolean isReachable0(byte[] addr, int scope, int timeout, byte[] inf, int ttl, int if_scope) throws IOException;
    
    public boolean isReachable(InetAddress addr, int timeout, NetworkInterface netif, int ttl) throws IOException {
        byte[] ifaddr = null;
        int scope = -1;
        int netif_scope = -1;
        if (netif != null) {
            java.util.Enumeration it = netif.getInetAddresses();
            InetAddress inetaddr = null;
            while (it.hasMoreElements()) {
                inetaddr = (InetAddress)(InetAddress)it.nextElement();
                if (inetaddr.getClass().isInstance(addr)) {
                    ifaddr = inetaddr.getAddress();
                    if (inetaddr instanceof Inet6Address) {
                        netif_scope = ((Inet6Address)(Inet6Address)inetaddr).getScopeId();
                    }
                    break;
                }
            }
            if (ifaddr == null) {
                return false;
            }
        }
        if (addr instanceof Inet6Address) scope = ((Inet6Address)(Inet6Address)addr).getScopeId();
        return isReachable0(addr.getAddress(), scope, timeout, ifaddr, ttl, netif_scope);
    }
    
    public synchronized InetAddress anyLocalAddress() {
        if (anyLocalAddress == null) {
            if (InetAddress.preferIPv6Address) {
                anyLocalAddress = new Inet6Address();
                anyLocalAddress.hostName = "::";
            } else {
                anyLocalAddress = (new Inet4AddressImpl()).anyLocalAddress();
            }
        }
        return anyLocalAddress;
    }
    
    public synchronized InetAddress loopbackAddress() {
        if (loopbackAddress == null) {
            if (InetAddress.preferIPv6Address) {
                byte[] loopback = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1};
                loopbackAddress = new Inet6Address("localhost", loopback);
            } else {
                loopbackAddress = (new Inet4AddressImpl()).loopbackAddress();
            }
        }
        return loopbackAddress;
    }
    private InetAddress anyLocalAddress;
    private InetAddress loopbackAddress;
}
