package java.rmi.server;

import java.io.*;
import java.net.*;

public interface RMIClientSocketFactory {
    
    public Socket createSocket(String host, int port) throws IOException;
}
