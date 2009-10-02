package java.util;

class RandomAccessSubList extends SubList implements RandomAccess {
    
    RandomAccessSubList(AbstractList list, int fromIndex, int toIndex) {
        super(list, fromIndex, toIndex);
    }
    
    public List subList(int fromIndex, int toIndex) {
        return new RandomAccessSubList(this, fromIndex, toIndex);
    }
}
