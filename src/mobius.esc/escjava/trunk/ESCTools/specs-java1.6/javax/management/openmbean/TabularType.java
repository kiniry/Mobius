package javax.management.openmbean;

import java.io.Serializable;
import java.util.List;
import java.util.Iterator;
import java.util.ArrayList;
import java.util.Collections;

public class TabularType extends OpenType implements Serializable {
    static final long serialVersionUID = 6554071860220659261L;
    private CompositeType rowType;
    private List indexNames;
    private transient Integer myHashCode = null;
    private transient String myToString = null;
    
    public TabularType(String typeName, String description, CompositeType rowType, String[] indexNames) throws OpenDataException {
        super(TabularData.class.getName(), typeName, description);
        if (rowType == null) {
            throw new IllegalArgumentException("Argument rowType cannot be null.");
        }
        checkForNullElement(indexNames, "indexNames");
        checkForEmptyString(indexNames, "indexNames");
        for (int i = 0; i < indexNames.length; i++) {
            if (!rowType.containsKey(indexNames[i])) {
                throw new OpenDataException("Argument\'s element value indexNames[" + i + "]=\"" + indexNames[i] + "\" is not a valid item name for rowType.");
            }
        }
        this.rowType = rowType;
        ArrayList tmpList = new ArrayList(indexNames.length + 1);
        for (int i = 0; i < indexNames.length; i++) {
            tmpList.add(indexNames[i]);
        }
        this.indexNames = Collections.unmodifiableList(tmpList);
    }
    
    private static void checkForNullElement(Object[] arg, String argName) {
        if ((arg == null) || (arg.length == 0)) {
            throw new IllegalArgumentException("Argument " + argName + "[] cannot be null or empty.");
        }
        for (int i = 0; i < arg.length; i++) {
            if (arg[i] == null) {
                throw new IllegalArgumentException("Argument\'s element " + argName + "[" + i + "] cannot be null.");
            }
        }
    }
    
    private static void checkForEmptyString(String[] arg, String argName) {
        for (int i = 0; i < arg.length; i++) {
            if (arg[i].trim().equals("")) {
                throw new IllegalArgumentException("Argument\'s element " + argName + "[" + i + "] cannot be an empty string.");
            }
        }
    }
    
    public CompositeType getRowType() {
        return rowType;
    }
    
    public List getIndexNames() {
        return indexNames;
    }
    
    public boolean isValue(Object obj) {
        if (obj == null) {
            return false;
        }
        TabularData value;
        try {
            value = (TabularData)(TabularData)obj;
        } catch (ClassCastException e) {
            return false;
        }
        return this.equals(value.getTabularType());
    }
    
    public boolean equals(Object obj) {
        if (obj == null) {
            return false;
        }
        TabularType other;
        try {
            other = (TabularType)(TabularType)obj;
        } catch (ClassCastException e) {
            return false;
        }
        if (!this.getTypeName().equals(other.getTypeName())) {
            return false;
        }
        if (!this.rowType.equals(other.rowType)) {
            return false;
        }
        if (!this.indexNames.equals(other.indexNames)) {
            return false;
        }
        return true;
    }
    
    public int hashCode() {
        if (myHashCode == null) {
            int value = 0;
            value += this.getTypeName().hashCode();
            value += this.rowType.hashCode();
            for (Iterator k = indexNames.iterator(); k.hasNext(); ) {
                value += k.next().hashCode();
            }
            myHashCode = new Integer(value);
        }
        return myHashCode.intValue();
    }
    
    public String toString() {
        if (myToString == null) {
            StringBuffer result = new StringBuffer().append(this.getClass().getName()).append("(name=").append(getTypeName()).append(",rowType=").append(rowType.toString()).append(",indexNames=(");
            int i = 0;
            Iterator k = indexNames.iterator();
            while (k.hasNext()) {
                if (i > 0) result.append(",");
                result.append(k.next().toString());
                i++;
            }
            result.append("))");
            myToString = result.toString();
        }
        return myToString;
    }
}
