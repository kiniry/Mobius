package java.util;

public interface Queue extends Collection {
    
    boolean offer(Object o);
    
    Object poll();
    
    Object remove();
    
    Object peek();
    
    Object element();
}
