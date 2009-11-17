package java.text;

public class FieldPosition {
    
    /*synthetic*/ static boolean access$200(FieldPosition x0, Format$Field x1, int x2) {
        return x0.matchesField(x1, x2);
    }
    
    /*synthetic*/ static boolean access$100(FieldPosition x0, Format$Field x1) {
        return x0.matchesField(x1);
    }
    {
    }
    int field = 0;
    int endIndex = 0;
    int beginIndex = 0;
    private Format$Field attribute;
    
    public FieldPosition(int field) {
        
        this.field = field;
    }
    
    public FieldPosition(Format$Field attribute) {
        this(attribute, -1);
    }
    
    public FieldPosition(Format$Field attribute, int fieldID) {
        
        this.attribute = attribute;
        this.field = fieldID;
    }
    
    public Format$Field getFieldAttribute() {
        return attribute;
    }
    
    public int getField() {
        return field;
    }
    
    public int getBeginIndex() {
        return beginIndex;
    }
    
    public int getEndIndex() {
        return endIndex;
    }
    
    public void setBeginIndex(int bi) {
        beginIndex = bi;
    }
    
    public void setEndIndex(int ei) {
        endIndex = ei;
    }
    
    Format$FieldDelegate getFieldDelegate() {
        return new FieldPosition$Delegate(this, null);
    }
    
    public boolean equals(Object obj) {
        if (obj == null) return false;
        if (!(obj instanceof FieldPosition)) return false;
        FieldPosition other = (FieldPosition)(FieldPosition)obj;
        if (attribute == null) {
            if (other.attribute != null) {
                return false;
            }
        } else if (!attribute.equals(other.attribute)) {
            return false;
        }
        return (beginIndex == other.beginIndex && endIndex == other.endIndex && field == other.field);
    }
    
    public int hashCode() {
        return (field << 24) | (beginIndex << 16) | endIndex;
    }
    
    public String toString() {
        return getClass().getName() + "[field=" + field + ",attribute=" + attribute + ",beginIndex=" + beginIndex + ",endIndex=" + endIndex + ']';
    }
    
    private boolean matchesField(Format$Field attribute) {
        if (this.attribute != null) {
            return this.attribute.equals(attribute);
        }
        return false;
    }
    
    private boolean matchesField(Format$Field attribute, int field) {
        if (this.attribute != null) {
            return this.attribute.equals(attribute);
        }
        return (field == this.field);
    }
    {
    }
}
