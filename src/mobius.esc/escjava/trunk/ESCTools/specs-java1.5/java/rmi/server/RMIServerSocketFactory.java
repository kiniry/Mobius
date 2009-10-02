package java.rmi.server;

import java.io.*;
import java.net.*;

public interface RMIServerSocketFactory {
    
    public ServerSocket createServerSocket(int port) throws IOException;
}
