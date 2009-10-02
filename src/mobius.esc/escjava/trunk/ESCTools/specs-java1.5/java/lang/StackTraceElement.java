package java.lang;

public final class StackTraceElement implements java.io.Serializable {
    private String declaringClass;
    private String methodName;
    private String fileName;
    private int lineNumber;
    
    public StackTraceElement(String declaringClass, String methodName, String fileName, int lineNumber) {
        
        if (declaringClass == null) throw new NullPointerException("Declaring class is null");
        if (methodName == null) throw new NullPointerException("Method name is null");
        this.declaringClass = declaringClass;
        this.methodName = methodName;
        this.fileName = fileName;
        this.lineNumber = lineNumber;
    }
    
    public String getFileName() {
        return fileName;
    }
    
    public int getLineNumber() {
        return lineNumber;
    }
    
    public String getClassName() {
        return declaringClass;
    }
    
    public String getMethodName() {
        return methodName;
    }
    
    public boolean isNativeMethod() {
        return lineNumber == -2;
    }
    
    public String toString() {
        return getClassName() + "." + methodName + (isNativeMethod() ? "(Native Method)" : (fileName != null && lineNumber >= 0 ? "(" + fileName + ":" + lineNumber + ")" : (fileName != null ? "(" + fileName + ")" : "(Unknown Source)")));
    }
    
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (!(obj instanceof StackTraceElement)) return false;
        StackTraceElement e = (StackTraceElement)(StackTraceElement)obj;
        return e.declaringClass.equals(declaringClass) && e.lineNumber == lineNumber && eq(methodName, e.methodName) && eq(fileName, e.fileName);
    }
    
    private static boolean eq(Object a, Object b) {
        return a == b || (a != null && a.equals(b));
    }
    
    public int hashCode() {
        int result = 31 * declaringClass.hashCode() + methodName.hashCode();
        result = 31 * result + (fileName == null ? 0 : fileName.hashCode());
        result = 31 * result + lineNumber;
        return result;
    }
    private static final long serialVersionUID = 6992337162326171013L;
}
