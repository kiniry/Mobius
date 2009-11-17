package java.lang;

import java.io.Serializable;
import java.io.IOException;
import java.io.InvalidObjectException;
import java.io.ObjectInputStream;
import java.io.ObjectStreamException;

public abstract class Enum implements Comparable, Serializable {
    private final String name;
    
    public final String name() {
        return name;
    }
    private final int ordinal;
    
    public final int ordinal() {
        return ordinal;
    }
    
    protected Enum(String name, int ordinal) {
        
        this.name = name;
        this.ordinal = ordinal;
    }
    
    public String toString() {
        return name;
    }
    
    public final boolean equals(Object other) {
        return this == other;
    }
    
    public final int hashCode() {
        return System.identityHashCode(this);
    }
    
    protected final Object clone() throws CloneNotSupportedException {
        throw new CloneNotSupportedException();
    }
    
    public final int compareTo(Enum o) {
        Enum other = (Enum)o;
        Enum self = this;
        if (self.getClass() != other.getClass() && self.getDeclaringClass() != other.getDeclaringClass()) throw new ClassCastException();
        return self.ordinal - other.ordinal;
    }
    
    public final Class getDeclaringClass() {
        Class clazz = getClass();
        Class zuper = clazz.getSuperclass();
        return (zuper == Enum.class) ? clazz : zuper;
    }
    
    public static Enum valueOf(Class enumType, String name) {
        Enum result = (Enum)enumType.enumConstantDirectory().get(name);
        if (result != null) return result;
        if (name == null) throw new NullPointerException("Name is null");
        throw new IllegalArgumentException("No enum const " + enumType + "." + name);
    }
    
    private void readObject(ObjectInputStream in) throws IOException, ClassNotFoundException {
        throw new InvalidObjectException("can\'t deserialize enum");
    }
    
    private void readObjectNoData() throws ObjectStreamException {
        throw new InvalidObjectException("can\'t deserialize enum");
    }
    
    /*synthetic*/ public int compareTo(Object x0) {
        return this.compareTo((Enum)x0);
    }
}
