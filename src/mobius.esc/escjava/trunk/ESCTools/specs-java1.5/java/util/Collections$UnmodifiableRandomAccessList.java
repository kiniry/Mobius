package java.util;

class Collections$UnmodifiableRandomAccessList extends Collections$UnmodifiableList implements RandomAccess {
    
    Collections$UnmodifiableRandomAccessList(List list) {
        super(list);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new Collections$UnmodifiableRandomAccessList(list.subList(fromIndex, toIndex));
    }
    private static final long serialVersionUID = -2542308836966382001L;
    
    private Object writeReplace() {
        return new Collections$UnmodifiableList(list);
    }
}
