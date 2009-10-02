package java.net;

import java.net.SocketException;
import java.util.Enumeration;
import sun.security.action.*;
import java.security.AccessController;

public final class NetworkInterface {
    
    /*synthetic*/ static InetAddress[] access$000(NetworkInterface x0) {
        return x0.addrs;
    }
    private String name;
    private String displayName;
    private int index;
    private InetAddress[] addrs;
    static {
        AccessController.doPrivileged(new LoadLibraryAction("net"));
        init();
    }
    
    NetworkInterface() {
        
    }
    
    NetworkInterface(String name, int index, InetAddress[] addrs) {
        
        this.name = name;
        this.index = index;
        this.addrs = addrs;
    }
    
    public String getName() {
        return name;
    }
    
    public Enumeration getInetAddresses() {
        {
        }
        return new NetworkInterface$1checkedAddresses(this);
    }
    
    int getIndex() {
        return index;
    }
    
    public String getDisplayName() {
        return displayName;
    }
    
    public static NetworkInterface getByName(String name) throws SocketException {
        if (name == null) throw new NullPointerException();
        return getByName0(name);
    }
    
    static native NetworkInterface getByIndex(int index) throws SocketException;
    
    public static NetworkInterface getByInetAddress(InetAddress addr) throws SocketException {
        if (addr == null) throw new NullPointerException();
        return getByInetAddress0(addr);
    }
    
    public static Enumeration getNetworkInterfaces() throws SocketException {
        final NetworkInterface[] netifs = getAll();
        if (netifs == null) return null;
        return new NetworkInterface$1(netifs);
    }
    
    private static native NetworkInterface[] getAll() throws SocketException;
    
    private static native NetworkInterface getByName0(String name) throws SocketException;
    
    private static native NetworkInterface getByInetAddress0(InetAddress addr) throws SocketException;
    
    public boolean equals(Object obj) {
        if ((obj == null) || !(obj instanceof NetworkInterface)) {
            return false;
        }
        NetworkInterface netIF = (NetworkInterface)(NetworkInterface)obj;
        if (name != null) {
            if (netIF.getName() != null) {
                if (!name.equals(netIF.getName())) {
                    return false;
                }
            } else {
                return false;
            }
        } else {
            if (netIF.getName() != null) {
                return false;
            }
        }
        Enumeration newAddrs = netIF.getInetAddresses();
        int i = 0;
        for (i = 0; newAddrs.hasMoreElements(); newAddrs.nextElement(), i++) ;
        if (addrs == null) {
            if (i != 0) {
                return false;
            }
        } else {
            int count = 0;
            Enumeration e = getInetAddresses();
            for (; e.hasMoreElements(); count++) {
                e.nextElement();
            }
            if (i != count) {
                return false;
            }
        }
        newAddrs = netIF.getInetAddresses();
        for (; newAddrs.hasMoreElements(); ) {
            boolean equal = false;
            Enumeration thisAddrs = getInetAddresses();
            InetAddress newAddr = (InetAddress)(InetAddress)newAddrs.nextElement();
            for (; thisAddrs.hasMoreElements(); ) {
                InetAddress thisAddr = (InetAddress)(InetAddress)thisAddrs.nextElement();
                if (thisAddr.equals(newAddr)) {
                    equal = true;
                }
            }
            if (!equal) {
                return false;
            }
        }
        return true;
    }
    
    public int hashCode() {
        int count = 0;
        if (addrs != null) {
            for (int i = 0; i < addrs.length; i++) {
                count += addrs[i].hashCode();
            }
        }
        return count;
    }
    
    public String toString() {
        String result = "name:";
        result += name == null ? "null" : name;
        if (displayName != null) {
            result += " (" + displayName + ")";
        }
        result += " index: " + index + " addresses:\n";
        for (Enumeration e = getInetAddresses(); e.hasMoreElements(); ) {
            InetAddress addr = (InetAddress)(InetAddress)e.nextElement();
            result += addr + ";\n";
        }
        return result;
    }
    
    private static native void init();
}
