package javax.management;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.ObjectStreamField;
import java.util.EventObject;
import java.security.AccessController;
import java.security.PrivilegedAction;
import com.sun.jmx.mbeanserver.GetPropertyAction;

public class Notification extends EventObject {
    private static final long oldSerialVersionUID = 1716977971058914352L;
    private static final long newSerialVersionUID = -7516092053498031989L;
    private static final ObjectStreamField[] oldSerialPersistentFields = {new ObjectStreamField("message", String.class), new ObjectStreamField("sequenceNumber", Long.TYPE), new ObjectStreamField("source", Object.class), new ObjectStreamField("sourceObjectName", ObjectName.class), new ObjectStreamField("timeStamp", Long.TYPE), new ObjectStreamField("type", String.class), new ObjectStreamField("userData", Object.class)};
    private static final ObjectStreamField[] newSerialPersistentFields = {new ObjectStreamField("message", String.class), new ObjectStreamField("sequenceNumber", Long.TYPE), new ObjectStreamField("source", Object.class), new ObjectStreamField("timeStamp", Long.TYPE), new ObjectStreamField("type", String.class), new ObjectStreamField("userData", Object.class)};
    private static final long serialVersionUID;
    private static final ObjectStreamField[] serialPersistentFields;
    private static boolean compat = false;
    static {
        try {
            PrivilegedAction act = new GetPropertyAction("jmx.serial.form");
            String form = (String)(String)AccessController.doPrivileged(act);
            compat = (form != null && form.equals("1.0"));
        } catch (Exception e) {
        }
        if (compat) {
            serialPersistentFields = oldSerialPersistentFields;
            serialVersionUID = oldSerialVersionUID;
        } else {
            serialPersistentFields = newSerialPersistentFields;
            serialVersionUID = newSerialVersionUID;
        }
    }
    private String type;
    private long sequenceNumber;
    private long timeStamp;
    private Object userData = null;
    private String message = "";
    protected Object source = null;
    
    public Notification(String type, Object source, long sequenceNumber) {
        super(source);
        this.source = source;
        this.type = type;
        this.sequenceNumber = sequenceNumber;
        this.timeStamp = (new java.util.Date()).getTime();
    }
    
    public Notification(String type, Object source, long sequenceNumber, String message) {
        super(source);
        this.source = source;
        this.type = type;
        this.sequenceNumber = sequenceNumber;
        this.timeStamp = (new java.util.Date()).getTime();
        this.message = message;
    }
    
    public Notification(String type, Object source, long sequenceNumber, long timeStamp) {
        super(source);
        this.source = source;
        this.type = type;
        this.sequenceNumber = sequenceNumber;
        this.timeStamp = timeStamp;
    }
    
    public Notification(String type, Object source, long sequenceNumber, long timeStamp, String message) {
        super(source);
        this.source = source;
        this.type = type;
        this.sequenceNumber = sequenceNumber;
        this.timeStamp = timeStamp;
        this.message = message;
    }
    
    public void setSource(Object source) {
        super.source = source;
        this.source = source;
    }
    
    public long getSequenceNumber() {
        return sequenceNumber;
    }
    
    public void setSequenceNumber(long sequenceNumber) {
        this.sequenceNumber = sequenceNumber;
    }
    
    public String getType() {
        return type;
    }
    
    public long getTimeStamp() {
        return timeStamp;
    }
    
    public void setTimeStamp(long timeStamp) {
        this.timeStamp = timeStamp;
    }
    
    public String getMessage() {
        return message;
    }
    
    public Object getUserData() {
        return userData;
    }
    
    public void setUserData(Object userData) {
        this.userData = userData;
    }
    
    public String toString() {
        return super.toString() + "[type=" + type + "][message=" + message + "]";
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        super.source = source;
    }
    
    private void writeObject(ObjectOutputStream out) throws IOException {
        if (compat) {
            ObjectOutputStream$PutField fields = out.putFields();
            fields.put("type", type);
            fields.put("sequenceNumber", sequenceNumber);
            fields.put("timeStamp", timeStamp);
            fields.put("userData", userData);
            fields.put("message", message);
            fields.put("source", source);
            out.writeFields();
        } else {
            out.defaultWriteObject();
        }
    }
}
