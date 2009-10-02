package java.net;

import java.io.IOException;

class Inet4AddressImpl implements InetAddressImpl {
    
    Inet4AddressImpl() {
        
    }
    
    public native String getLocalHostName() throws UnknownHostException;
    
    public native byte[][] lookupAllHostAddr(String hostname) throws UnknownHostException;
    
    public native String getHostByAddr(byte[] addr) throws UnknownHostException;
    
    private native boolean isReachable0(byte[] addr, int timeout, byte[] ifaddr, int ttl) throws IOException;
    
    public synchronized InetAddress anyLocalAddress() {
        if (anyLocalAddress == null) {
            anyLocalAddress = new Inet4Address();
            anyLocalAddress.hostName = "0.0.0.0";
        }
        return anyLocalAddress;
    }
    
    public synchronized InetAddress loopbackAddress() {
        if (loopbackAddress == null) {
            byte[] loopback = {127, 0, 0, 1};
            loopbackAddress = new Inet4Address("localhost", loopback);
        }
        return loopbackAddress;
    }
    
    public boolean isReachable(InetAddress addr, int timeout, NetworkInterface netif, int ttl) throws IOException {
        byte[] ifaddr = null;
        if (netif != null) {
            java.util.Enumeration it = netif.getInetAddresses();
            InetAddress inetaddr = null;
            while (!(inetaddr instanceof Inet4Address) && it.hasMoreElements()) inetaddr = (InetAddress)(InetAddress)it.nextElement();
            if (inetaddr instanceof Inet4Address) ifaddr = inetaddr.getAddress();
        }
        return isReachable0(addr.getAddress(), timeout, ifaddr, ttl);
    }
    private InetAddress anyLocalAddress;
    private InetAddress loopbackAddress;
}
