package java.rmi.server;

import java.rmi.*;
import java.io.ObjectOutput;
import java.io.ObjectInput;
import java.io.StreamCorruptedException;
import java.io.IOException;


public interface RemoteCall {
    
    
    ObjectOutput getOutputStream() throws IOException;
    
    
    void releaseOutputStream() throws IOException;
    
    
    ObjectInput getInputStream() throws IOException;
    
    
    void releaseInputStream() throws IOException;
    
    
    ObjectOutput getResultStream(boolean success) throws IOException, StreamCorruptedException;
    
    
    void executeCall() throws Exception;
    
    
    void done() throws IOException;
}
