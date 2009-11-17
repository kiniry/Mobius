package javax.print;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;

public class DocFlavor implements Serializable, Cloneable {
    private static final long serialVersionUID = -4512080796965449721L;
    public static final String hostEncoding;
    static {
        hostEncoding = (String)(String)java.security.AccessController.doPrivileged(new sun.security.action.GetPropertyAction("file.encoding"));
    }
    private transient MimeType myMimeType;
    private String myClassName;
    private transient String myStringValue = null;
    
    public DocFlavor(String mimeType, String className) {
        
        if (className == null) {
            throw new NullPointerException();
        }
        myMimeType = new MimeType(mimeType);
        myClassName = className;
    }
    
    public String getMimeType() {
        return myMimeType.getMimeType();
    }
    
    public String getMediaType() {
        return myMimeType.getMediaType();
    }
    
    public String getMediaSubtype() {
        return myMimeType.getMediaSubtype();
    }
    
    public String getParameter(String paramName) {
        return (String)(String)myMimeType.getParameterMap().get(paramName.toLowerCase());
    }
    
    public String getRepresentationClassName() {
        return myClassName;
    }
    
    public String toString() {
        return getStringValue();
    }
    
    public int hashCode() {
        return getStringValue().hashCode();
    }
    
    public boolean equals(Object obj) {
        return obj != null && obj instanceof DocFlavor && getStringValue().equals(((DocFlavor)(DocFlavor)obj).getStringValue());
    }
    
    private String getStringValue() {
        if (myStringValue == null) {
            myStringValue = myMimeType + "; class=\"" + myClassName + "\"";
        }
        return myStringValue;
    }
    
    private void writeObject(ObjectOutputStream s) throws IOException {
        s.defaultWriteObject();
        s.writeObject(myMimeType.getMimeType());
    }
    
    private void readObject(ObjectInputStream s) throws ClassNotFoundException, IOException {
        s.defaultReadObject();
        myMimeType = new MimeType((String)(String)s.readObject());
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
    {
    }
}
