package javax.management.openmbean;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public abstract class OpenType implements Serializable {
    static final long serialVersionUID = -9195195325186646468L;
    static final List ALLOWED_CLASSNAMES_LIST = Collections.unmodifiableList(Arrays.asList(new String[]{"java.lang.Void", "java.lang.Boolean", "java.lang.Character", "java.lang.Byte", "java.lang.Short", "java.lang.Integer", "java.lang.Long", "java.lang.Float", "java.lang.Double", "java.lang.String", "java.math.BigDecimal", "java.math.BigInteger", "java.util.Date", "javax.management.ObjectName", CompositeData.class.getName(), TabularData.class.getName()}));
    public static final String[] ALLOWED_CLASSNAMES = (String[])ALLOWED_CLASSNAMES_LIST.toArray(new String[0]);
    private String className;
    private String description;
    private String typeName;
    private transient boolean isArray = false;
    
    protected OpenType(String className, String typeName, String description) throws OpenDataException {
        
        if ((className == null) || (className.trim().equals(""))) {
            throw new IllegalArgumentException("Argument className cannot be null or empty.");
        }
        if ((typeName == null) || (typeName.trim().equals(""))) {
            throw new IllegalArgumentException("Argument typeName cannot be null or empty.");
        }
        if ((description == null) || (description.trim().equals(""))) {
            throw new IllegalArgumentException("Argument description cannot be null or empty.");
        }
        className = className.trim();
        typeName = typeName.trim();
        description = description.trim();
        int n = 0;
        while (className.startsWith("[", n)) {
            n++;
        }
        String eltClassName;
        boolean isArray = false;
        if (n > 0) {
            eltClassName = className.substring(n + 1, className.length() - 1);
            isArray = true;
        } else {
            eltClassName = className;
        }
        if (!ALLOWED_CLASSNAMES_LIST.contains(eltClassName)) {
            throw new OpenDataException("Argument className=\"" + className + "\" is not one of the allowed Java class names for open data.");
        }
        this.className = className;
        this.typeName = typeName;
        this.description = description;
        this.isArray = isArray;
    }
    
    public String getClassName() {
        return className;
    }
    
    public String getTypeName() {
        return typeName;
    }
    
    public String getDescription() {
        return description;
    }
    
    public boolean isArray() {
        return isArray;
    }
    
    public abstract boolean isValue(Object obj);
    
    public abstract boolean equals(Object obj);
    
    public abstract int hashCode();
    
    public abstract String toString();
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        isArray = (className.startsWith("["));
    }
}
