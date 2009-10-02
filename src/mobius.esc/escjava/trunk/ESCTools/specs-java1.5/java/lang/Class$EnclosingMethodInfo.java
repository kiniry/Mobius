package java.lang;

import sun.reflect.annotation.*;

final class Class$EnclosingMethodInfo {
    
    /*synthetic*/ Class$EnclosingMethodInfo(Object[] x0, java.lang.Class$1 x1) {
        this(x0);
    }
    /*synthetic*/ static final boolean $assertionsDisabled = !Class.class.desiredAssertionStatus();
    private Class enclosingClass;
    private String name;
    private String descriptor;
    
    private Class$EnclosingMethodInfo(Object[] enclosingInfo) {
        
        if (enclosingInfo.length != 3) throw new InternalError("Malformed enclosing method information");
        try {
            enclosingClass = (Class)(Class)enclosingInfo[0];
            if (!$assertionsDisabled && !(enclosingClass != null)) throw new AssertionError();
            name = (String)(String)enclosingInfo[1];
            descriptor = (String)(String)enclosingInfo[2];
            if (!$assertionsDisabled && !((name != null && descriptor != null) || name == descriptor)) throw new AssertionError();
        } catch (ClassCastException cce) {
            throw new InternalError("Invalid type in enclosing method information");
        }
    }
    
    boolean isPartial() {
        return enclosingClass == null || name == null || descriptor == null;
    }
    
    boolean isConstructor() {
        return !isPartial() && "<init>".equals(name);
    }
    
    boolean isMethod() {
        return !isPartial() && !isConstructor() && !"<clinit>".equals(name);
    }
    
    Class getEnclosingClass() {
        return enclosingClass;
    }
    
    String getName() {
        return name;
    }
    
    String getDescriptor() {
        return descriptor;
    }
}
