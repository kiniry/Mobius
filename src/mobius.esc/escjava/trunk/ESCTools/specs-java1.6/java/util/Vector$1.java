package java.util;

class Vector$1 implements Enumeration {
    /*synthetic*/ final Vector this$0;
    
    Vector$1(/*synthetic*/ final Vector this$0) {
        this.this$0 = this$0;
        
    }
    int count = 0;
    
    public boolean hasMoreElements() {
        return count < this$0.elementCount;
    }
    
    public Object nextElement() {
        synchronized (this$0) {
            if (count < this$0.elementCount) {
                return (Object)this$0.elementData[count++];
            }
        }
        throw new NoSuchElementException("Vector Enumeration");
    }
}
