package javax.management;

import java.util.ArrayList;

public class AttributeList extends ArrayList {
    private static final long serialVersionUID = -4077085769279709076L;
    
    public AttributeList() {
        
    }
    
    public AttributeList(int initialCapacity) {
        super(initialCapacity);
    }
    
    public AttributeList(AttributeList list) {
        super(list);
    }
    
    public void add(Attribute object) {
        super.add(object);
    }
    
    public void add(int index, Attribute object) {
        try {
            super.add(index, object);
        } catch (IndexOutOfBoundsException e) {
            throw (new RuntimeOperationsException(e, "The specified index is out of range"));
        }
    }
    
    public void set(int index, Attribute object) {
        try {
            super.set(index, object);
        } catch (IndexOutOfBoundsException e) {
            throw (new RuntimeOperationsException(e, "The specified index is out of range"));
        }
    }
    
    public boolean addAll(AttributeList list) {
        return (super.addAll(list));
    }
    
    public boolean addAll(int index, AttributeList list) {
        try {
            return (super.addAll(index, list));
        } catch (IndexOutOfBoundsException e) {
            throw (new RuntimeOperationsException(e, "The specified index is out of range"));
        }
    }
}
