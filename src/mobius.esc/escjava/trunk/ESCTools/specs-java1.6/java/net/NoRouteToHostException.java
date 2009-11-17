package java.net;

public class NoRouteToHostException extends SocketException {
    
    public NoRouteToHostException(String msg) {
        super(msg);
    }
    
    public NoRouteToHostException() {
        
    }
}
