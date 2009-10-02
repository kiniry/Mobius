package java.awt.dnd;

import java.io.ObjectOutputStream;
import java.io.IOException;
import java.io.Serializable;

final class SerializationTester {
    private static ObjectOutputStream stream;
    static {
        try {
            stream = new ObjectOutputStream(new SerializationTester$1());
        } catch (IOException cannotHappen) {
        }
    }
    
    static boolean test(Object obj) {
        if (!(obj instanceof Serializable)) {
            return false;
        }
        try {
            stream.writeObject(obj);
        } catch (IOException e) {
            return false;
        } finally {
            try {
                stream.reset();
            } catch (IOException e) {
            }
        }
        return true;
    }
    
    private SerializationTester() {
        
    }
}
