package java.util;

import java.io.NotSerializableException;
import java.io.IOException;

public class InvalidPropertiesFormatException extends IOException {
    
    public InvalidPropertiesFormatException(Throwable cause) {
        super(cause == null ? null : cause.toString());
        this.initCause(cause);
    }
    
    public InvalidPropertiesFormatException(String message) {
        super(message);
    }
    
    private void writeObject(java.io.ObjectOutputStream out) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
    
    private void readObject(java.io.ObjectInputStream in) throws NotSerializableException {
        throw new NotSerializableException("Not serializable.");
    }
}
