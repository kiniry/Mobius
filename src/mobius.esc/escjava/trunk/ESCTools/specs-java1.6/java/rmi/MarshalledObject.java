package java.rmi;

import java.io.*;

public final class MarshalledObject implements Serializable {
    private byte[] objBytes = null;
    private byte[] locBytes = null;
    private int hash;
    private static final long serialVersionUID = 8988374069173025854L;
    
    public MarshalledObject(Object obj) throws java.io.IOException {
        
        if (obj == null) {
            hash = 13;
            return;
        }
        ByteArrayOutputStream bout = new ByteArrayOutputStream();
        ByteArrayOutputStream lout = new ByteArrayOutputStream();
        MarshalledObject$MarshalledObjectOutputStream out = new MarshalledObject$MarshalledObjectOutputStream(bout, lout);
        out.writeObject(obj);
        out.flush();
        objBytes = bout.toByteArray();
        locBytes = (out.hadAnnotations() ? lout.toByteArray() : null);
        int h = 0;
        for (int i = 0; i < objBytes.length; i++) {
            h = 31 * h + objBytes[i];
        }
        hash = h;
    }
    
    public Object get() throws java.io.IOException, java.lang.ClassNotFoundException {
        if (objBytes == null) return null;
        ByteArrayInputStream bin = new ByteArrayInputStream(objBytes);
        ByteArrayInputStream lin = (locBytes == null ? null : new ByteArrayInputStream(locBytes));
        MarshalledObject$MarshalledObjectInputStream in = new MarshalledObject$MarshalledObjectInputStream(bin, lin);
        Object obj = in.readObject();
        in.close();
        return obj;
    }
    
    public int hashCode() {
        return hash;
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (obj != null && obj instanceof MarshalledObject) {
            MarshalledObject other = (MarshalledObject)(MarshalledObject)obj;
            if (objBytes == null || other.objBytes == null) return objBytes == other.objBytes;
            if (objBytes.length != other.objBytes.length) return false;
            for (int i = 0; i < objBytes.length; ++i) {
                if (objBytes[i] != other.objBytes[i]) return false;
            }
            return true;
        } else {
            return false;
        }
    }
    {
    }
    {
    }
}
