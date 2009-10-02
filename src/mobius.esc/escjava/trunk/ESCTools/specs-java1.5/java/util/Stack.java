package java.util;

public class Stack extends Vector {
    
    public Stack() {
        
    }
    
    public Object push(Object item) {
        addElement(item);
        return item;
    }
    
    public synchronized Object pop() {
        Object obj;
        int len = size();
        obj = peek();
        removeElementAt(len - 1);
        return obj;
    }
    
    public synchronized Object peek() {
        int len = size();
        if (len == 0) throw new EmptyStackException();
        return elementAt(len - 1);
    }
    
    public boolean empty() {
        return size() == 0;
    }
    
    public synchronized int search(Object o) {
        int i = lastIndexOf(o);
        if (i >= 0) {
            return size() - i;
        }
        return -1;
    }
    private static final long serialVersionUID = 1224463164541339165L;
}
