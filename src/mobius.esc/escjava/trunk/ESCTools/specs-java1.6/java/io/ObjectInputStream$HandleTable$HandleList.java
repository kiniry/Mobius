package java.io;

class ObjectInputStream$HandleTable$HandleList {
    private int[] list = new int[4];
    private int size = 0;
    
    public ObjectInputStream$HandleTable$HandleList() {
        
    }
    
    public void add(int handle) {
        if (size >= list.length) {
            int[] newList = new int[list.length << 1];
            System.arraycopy(list, 0, newList, 0, list.length);
            list = newList;
        }
        list[size++] = handle;
    }
    
    public int get(int index) {
        if (index >= size) {
            throw new ArrayIndexOutOfBoundsException();
        }
        return list[index];
    }
    
    public int size() {
        return size;
    }
}
