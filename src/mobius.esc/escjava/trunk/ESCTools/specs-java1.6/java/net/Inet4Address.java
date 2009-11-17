package java.net;

import java.io.ObjectStreamException;
import sun.security.action.*;

public final class Inet4Address extends InetAddress {
    static final int INADDRSZ = 4;
    private static final long serialVersionUID = 3286316764910316507L;
    static {
        init();
    }
    
    Inet4Address() {
        
        hostName = null;
        address = 0;
        family = IPv4;
    }
    
    Inet4Address(String hostName, byte[] addr) {
        
        this.hostName = hostName;
        this.family = IPv4;
        if (addr != null) {
            if (addr.length == INADDRSZ) {
                address = addr[3] & 255;
                address |= ((addr[2] << 8) & 65280);
                address |= ((addr[1] << 16) & 16711680);
                address |= ((addr[0] << 24) & -16777216);
            }
        }
    }
    
    Inet4Address(String hostName, int address) {
        
        this.hostName = hostName;
        this.family = IPv4;
        this.address = address;
    }
    
    private Object writeReplace() throws ObjectStreamException {
        InetAddress inet = new InetAddress();
        inet.hostName = this.hostName;
        inet.address = this.address;
        inet.family = 2;
        return inet;
    }
    
    public boolean isMulticastAddress() {
        return ((address & -268435456) == -536870912);
    }
    
    public boolean isAnyLocalAddress() {
        return address == 0;
    }
    private static final int loopback = 2130706433;
    
    public boolean isLoopbackAddress() {
        byte[] byteAddr = getAddress();
        return byteAddr[0] == 127;
    }
    
    public boolean isLinkLocalAddress() {
        return (((address >>> 24) & 255) == 169) && (((address >>> 16) & 255) == 254);
    }
    
    public boolean isSiteLocalAddress() {
        return (((address >>> 24) & 255) == 10) || ((((address >>> 24) & 255) == 172) && (((address >>> 16) & 240) == 16)) || ((((address >>> 24) & 255) == 192) && (((address >>> 16) & 255) == 168));
    }
    
    public boolean isMCGlobal() {
        byte[] byteAddr = getAddress();
        return ((byteAddr[0] & 255) >= 224 && (byteAddr[0] & 255) <= 238) && !((byteAddr[0] & 255) == 224 && byteAddr[1] == 0 && byteAddr[2] == 0);
    }
    
    public boolean isMCNodeLocal() {
        return false;
    }
    
    public boolean isMCLinkLocal() {
        return (((address >>> 24) & 255) == 224) && (((address >>> 16) & 255) == 0) && (((address >>> 8) & 255) == 0);
    }
    
    public boolean isMCSiteLocal() {
        return (((address >>> 24) & 255) == 239) && (((address >>> 16) & 255) == 255);
    }
    
    public boolean isMCOrgLocal() {
        return (((address >>> 24) & 255) == 239) && (((address >>> 16) & 255) >= 192) && (((address >>> 16) & 255) <= 195);
    }
    
    public byte[] getAddress() {
        byte[] addr = new byte[INADDRSZ];
        addr[0] = (byte)((address >>> 24) & 255);
        addr[1] = (byte)((address >>> 16) & 255);
        addr[2] = (byte)((address >>> 8) & 255);
        addr[3] = (byte)(address & 255);
        return addr;
    }
    
    public String getHostAddress() {
        return numericToTextFormat(getAddress());
    }
    
    public int hashCode() {
        return address;
    }
    
    public boolean equals(Object obj) {
        return (obj != null) && (obj instanceof Inet4Address) && (((InetAddress)(InetAddress)obj).address == address);
    }
    
    static String numericToTextFormat(byte[] src) {
        return (src[0] & 255) + "." + (src[1] & 255) + "." + (src[2] & 255) + "." + (src[3] & 255);
    }
    
    private static native void init();
}
