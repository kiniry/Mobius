package java.net;

import java.io.IOException;

public class ProtocolException extends IOException {
    
    public ProtocolException(String host) {
        super(host);
    }
    
    public ProtocolException() {
        
    }
}
