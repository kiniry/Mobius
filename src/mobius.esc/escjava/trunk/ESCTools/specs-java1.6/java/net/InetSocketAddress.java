package java.net;

import java.io.ObjectInputStream;
import java.io.IOException;
import java.io.InvalidObjectException;

public class InetSocketAddress extends SocketAddress {
    private String hostname = null;
    private InetAddress addr = null;
    private int port;
    private static final long serialVersionUID = 5076001401234631237L;
    
    private InetSocketAddress() {
        
    }
    
    public InetSocketAddress(int port) {
        this(InetAddress.anyLocalAddress(), port);
    }
    
    public InetSocketAddress(InetAddress addr, int port) {
        
        if (port < 0 || port > 65535) {
            throw new IllegalArgumentException("port out of range:" + port);
        }
        this.port = port;
        if (addr == null) this.addr = InetAddress.anyLocalAddress(); else this.addr = addr;
    }
    
    public InetSocketAddress(String hostname, int port) {
        
        if (port < 0 || port > 65535) {
            throw new IllegalArgumentException("port out of range:" + port);
        }
        if (hostname == null) {
            throw new IllegalArgumentException("hostname can\'t be null");
        }
        try {
            addr = InetAddress.getByName(hostname);
        } catch (UnknownHostException e) {
            this.hostname = hostname;
            addr = null;
        }
        this.port = port;
    }
    
    public static InetSocketAddress createUnresolved(String host, int port) {
        if (port < 0 || port > 65535) {
            throw new IllegalArgumentException("port out of range:" + port);
        }
        if (host == null) {
            throw new IllegalArgumentException("hostname can\'t be null");
        }
        InetSocketAddress s = new InetSocketAddress();
        s.port = port;
        s.hostname = host;
        s.addr = null;
        return s;
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (port < 0 || port > 65535) {
            throw new InvalidObjectException("port out of range:" + port);
        }
        if (hostname == null && addr == null) {
            throw new InvalidObjectException("hostname and addr can\'t both be null");
        }
    }
    
    public final int getPort() {
        return port;
    }
    
    public final InetAddress getAddress() {
        return addr;
    }
    
    public final String getHostName() {
        if (hostname != null) return hostname;
        if (addr != null) return addr.getHostName();
        return null;
    }
    
    final String getHostString() {
        if (hostname != null) return hostname;
        if (addr != null) {
            if (addr.hostName != null) return addr.hostName; else return addr.getHostAddress();
        }
        return null;
    }
    
    public final boolean isUnresolved() {
        return addr == null;
    }
    
    public String toString() {
        if (isUnresolved()) {
            return hostname + ":" + port;
        } else {
            return addr.toString() + ":" + port;
        }
    }
    
    public final boolean equals(Object obj) {
        if (obj == null || !(obj instanceof InetSocketAddress)) return false;
        InetSocketAddress sockAddr = (InetSocketAddress)(InetSocketAddress)obj;
        boolean sameIP = false;
        if (this.addr != null) sameIP = this.addr.equals(sockAddr.addr); else if (this.hostname != null) sameIP = (sockAddr.addr == null) && this.hostname.equals(sockAddr.hostname); else sameIP = (sockAddr.addr == null) && (sockAddr.hostname == null);
        return sameIP && (this.port == sockAddr.port);
    }
    
    public final int hashCode() {
        if (addr != null) return addr.hashCode() + port;
        if (hostname != null) return hostname.hashCode() + port;
        return port;
    }
}
