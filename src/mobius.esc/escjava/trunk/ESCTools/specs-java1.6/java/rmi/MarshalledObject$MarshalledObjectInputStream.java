package java.rmi;

import java.io.*;
import sun.rmi.server.MarshalInputStream;

class MarshalledObject$MarshalledObjectInputStream extends MarshalInputStream {
    private ObjectInputStream locIn;
    
    MarshalledObject$MarshalledObjectInputStream(InputStream objIn, InputStream locIn) throws IOException {
        super(objIn);
        this.locIn = (locIn == null ? null : new ObjectInputStream(locIn));
    }
    
    protected Object readLocation() throws IOException, ClassNotFoundException {
        return (locIn == null ? null : locIn.readObject());
    }
}
