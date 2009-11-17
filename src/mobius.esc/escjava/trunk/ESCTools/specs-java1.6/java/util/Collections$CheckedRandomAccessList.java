package java.util;

class Collections$CheckedRandomAccessList extends Collections$CheckedList implements RandomAccess {
    private static final long serialVersionUID = 1638200125423088369L;
    
    Collections$CheckedRandomAccessList(List list, Class type) {
        super(list, type);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new Collections$CheckedRandomAccessList(list.subList(fromIndex, toIndex), type);
    }
}
