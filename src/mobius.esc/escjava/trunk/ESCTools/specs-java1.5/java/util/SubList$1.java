package java.util;

class SubList$1 implements ListIterator {
    /*synthetic*/ final SubList this$0;
    /*synthetic*/ final int val$index;
    
    SubList$1(/*synthetic*/ final SubList this$0, /*synthetic*/ final int val$index) {
        this.this$0 = this$0;
        this.val$index = val$index;
        
    }
    private ListIterator i = SubList.access$100(this$0).listIterator(val$index + SubList.access$000(this$0));
    
    public boolean hasNext() {
        return nextIndex() < SubList.access$200(this$0);
    }
    
    public Object next() {
        if (hasNext()) return i.next(); else throw new NoSuchElementException();
    }
    
    public boolean hasPrevious() {
        return previousIndex() >= 0;
    }
    
    public Object previous() {
        if (hasPrevious()) return i.previous(); else throw new NoSuchElementException();
    }
    
    public int nextIndex() {
        return i.nextIndex() - SubList.access$000(this$0);
    }
    
    public int previousIndex() {
        return i.previousIndex() - SubList.access$000(this$0);
    }
    
    public void remove() {
        i.remove();
        SubList.access$302(this$0, SubList.access$100(this$0).modCount);
        SubList.access$210(this$0);
        this$0.modCount++;
    }
    
    public void set(Object o) {
        i.set(o);
    }
    
    public void add(Object o) {
        i.add(o);
        SubList.access$302(this$0, SubList.access$100(this$0).modCount);
        SubList.access$208(this$0);
        this$0.modCount++;
    }
}
