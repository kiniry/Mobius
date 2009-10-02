package java.io;

import java.io.ObjectOutput;
import java.io.ObjectInput;

public interface Externalizable extends java.io.Serializable {
    
    void writeExternal(ObjectOutput out) throws IOException;
    
    void readExternal(ObjectInput in) throws IOException, ClassNotFoundException;
}
