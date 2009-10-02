package java.rmi;

import java.io.*;
import sun.rmi.server.MarshalOutputStream;

class MarshalledObject$MarshalledObjectOutputStream extends MarshalOutputStream {
    private ObjectOutputStream locOut;
    private boolean hadAnnotations;
    
    MarshalledObject$MarshalledObjectOutputStream(OutputStream objOut, OutputStream locOut) throws IOException {
        super(objOut);
        this.useProtocolVersion(ObjectStreamConstants.PROTOCOL_VERSION_2);
        this.locOut = new ObjectOutputStream(locOut);
        hadAnnotations = false;
    }
    
    boolean hadAnnotations() {
        return hadAnnotations;
    }
    
    protected void writeLocation(String loc) throws IOException {
        hadAnnotations |= (loc != null);
        locOut.writeObject(loc);
    }
    
    public void flush() throws IOException {
        super.flush();
        locOut.flush();
    }
}
