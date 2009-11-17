package java.rmi.server;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;
import java.security.SecureRandom;
import java.util.Random;

public final class ObjID implements java.io.Serializable {
    {
    }
    public static final int REGISTRY_ID = 0;
    public static final int ACTIVATOR_ID = 1;
    public static final int DGC_ID = 2;
    private static final long serialVersionUID = -6386392263968365220L;
    private static final UID mySpace;
    private static final Random generator;
    private final long objNum;
    private final UID space;
    
    public ObjID() {
        
        space = (mySpace != null) ? mySpace : new UID();
        objNum = generator.nextLong();
    }
    
    public ObjID(int objNum) {
        
        space = new UID((short)0);
        this.objNum = objNum;
    }
    
    private ObjID(long objNum, UID space) {
        
        this.objNum = objNum;
        this.space = space;
    }
    
    public void write(ObjectOutput out) throws IOException {
        out.writeLong(objNum);
        space.write(out);
    }
    
    public static ObjID read(ObjectInput in) throws IOException {
        long num = in.readLong();
        UID space = UID.read(in);
        return new ObjID(num, space);
    }
    
    public int hashCode() {
        return (int)objNum;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof ObjID) {
            ObjID id = (ObjID)(ObjID)obj;
            return objNum == id.objNum && space.equals(id.space);
        } else {
            return false;
        }
    }
    
    public String toString() {
        return "[" + (space.equals(mySpace) ? "" : space + ", ") + objNum + "]";
    }
    {
    }
    static {
        boolean randomIDs = ((Boolean)(Boolean)java.security.AccessController.doPrivileged(new sun.security.action.GetBooleanAction("java.rmi.server.randomIDs"))).booleanValue();
        if (randomIDs) {
            generator = new SecureRandom();
            mySpace = null;
        } else {
            generator = new ObjID$InsecureRandom(null);
            mySpace = new UID();
        }
    }
}
