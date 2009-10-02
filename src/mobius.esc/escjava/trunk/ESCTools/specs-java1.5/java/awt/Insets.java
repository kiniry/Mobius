package java.awt;

public class Insets implements Cloneable, java.io.Serializable {
    public int top;
    public int left;
    public int bottom;
    public int right;
    private static final long serialVersionUID = -2272572637695466749L;
    static {
        Toolkit.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    public Insets(int top, int left, int bottom, int right) {
        
        this.top = top;
        this.left = left;
        this.bottom = bottom;
        this.right = right;
    }
    
    public void set(int top, int left, int bottom, int right) {
        this.top = top;
        this.left = left;
        this.bottom = bottom;
        this.right = right;
    }
    
    public boolean equals(Object obj) {
        if (obj instanceof Insets) {
            Insets insets = (Insets)(Insets)obj;
            return ((top == insets.top) && (left == insets.left) && (bottom == insets.bottom) && (right == insets.right));
        }
        return false;
    }
    
    public int hashCode() {
        int sum1 = left + bottom;
        int sum2 = right + top;
        int val1 = sum1 * (sum1 + 1) / 2 + left;
        int val2 = sum2 * (sum2 + 1) / 2 + top;
        int sum3 = val1 + val2;
        return sum3 * (sum3 + 1) / 2 + val2;
    }
    
    public String toString() {
        return getClass().getName() + "[top=" + top + ",left=" + left + ",bottom=" + bottom + ",right=" + right + "]";
    }
    
    public Object clone() {
        try {
            return super.clone();
        } catch (CloneNotSupportedException e) {
            throw new InternalError();
        }
    }
    
    private static native void initIDs();
}
