package java.rmi.server;

public interface RMIFailureHandler {
    
    public boolean failure(Exception ex);
}
