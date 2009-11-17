package java.net;

import java.io.IOException;

interface InetAddressImpl {
    
    String getLocalHostName() throws UnknownHostException;
    
    byte[][] lookupAllHostAddr(String hostname) throws UnknownHostException;
    
    String getHostByAddr(byte[] addr) throws UnknownHostException;
    
    InetAddress anyLocalAddress();
    
    InetAddress loopbackAddress();
    
    boolean isReachable(InetAddress addr, int timeout, NetworkInterface netif, int ttl) throws IOException;
}
