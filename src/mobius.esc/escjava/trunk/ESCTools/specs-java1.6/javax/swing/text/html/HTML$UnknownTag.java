package javax.swing.text.html;

import java.io.*;

public class HTML$UnknownTag extends HTML$Tag implements Serializable {
    
    public HTML$UnknownTag(String id) {
        super(id);
    }
    
    public int hashCode() {
        return toString().hashCode();
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof HTML$UnknownTag) {
            return toString().equals(obj.toString());
        }
        return false;
    }
    
    private void writeObject(java.io.ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeBoolean(blockTag);
        s.writeBoolean(breakTag);
        s.writeBoolean(unknown);
        s.writeObject(name);
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        blockTag = s.readBoolean();
        breakTag = s.readBoolean();
        unknown = s.readBoolean();
        name = (String)(String)s.readObject();
    }
}
