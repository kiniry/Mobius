package java.rmi.dgc;

import java.io.*;
import java.net.*;
import java.security.*;

class VMID$1 implements PrivilegedAction {
    
    VMID$1() {
        
    }
    
    public Object run() {
        try {
            return InetAddress.getLocalHost().getAddress();
        } catch (Exception e) {
        }
        return new byte[]{0, 0, 0, 0};
    }
}
