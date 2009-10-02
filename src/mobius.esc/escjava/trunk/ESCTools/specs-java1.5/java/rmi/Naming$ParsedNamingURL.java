package java.rmi;

import java.rmi.registry.*;

class Naming$ParsedNamingURL {
    String host;
    int port;
    String name;
    
    Naming$ParsedNamingURL(String host, int port, String name) {
        
        this.host = host;
        this.port = port;
        this.name = name;
    }
}
