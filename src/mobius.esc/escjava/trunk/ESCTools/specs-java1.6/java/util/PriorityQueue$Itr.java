package java.util;

class PriorityQueue$Itr implements Iterator {
    
    /*synthetic*/ PriorityQueue$Itr(PriorityQueue x0, java.util.PriorityQueue$1 x1) {
        this(x0);
    }
    /*synthetic*/ final PriorityQueue this$0;
    
    private PriorityQueue$Itr(/*synthetic*/ final PriorityQueue this$0) {
        this.this$0 = this$0;
        
    }
    private int cursor = 1;
    private int lastRet = 0;
    private int expectedModCount = PriorityQueue.access$100(this$0);
    private ArrayList forgetMeNot = null;
    private Object lastRetElt = null;
    
    public boolean hasNext() {
        return cursor <= PriorityQueue.access$200(this$0) || forgetMeNot != null;
    }
    
    public Object next() {
        checkForComodification();
        Object result;
        if (cursor <= PriorityQueue.access$200(this$0)) {
            result = (Object)PriorityQueue.access$300(this$0)[cursor];
            lastRet = cursor++;
        } else if (forgetMeNot == null) throw new NoSuchElementException(); else {
            int remaining = forgetMeNot.size();
            result = forgetMeNot.remove(remaining - 1);
            if (remaining == 1) forgetMeNot = null;
            lastRet = 0;
            lastRetElt = result;
        }
        return result;
    }
    
    public void remove() {
        checkForComodification();
        if (lastRet != 0) {
            Object moved = PriorityQueue.access$400(this$0, lastRet);
            lastRet = 0;
            if (moved == null) {
                cursor--;
            } else {
                if (forgetMeNot == null) forgetMeNot = new ArrayList();
                forgetMeNot.add(moved);
            }
        } else if (lastRetElt != null) {
            this$0.remove(lastRetElt);
            lastRetElt = null;
        } else {
            throw new IllegalStateException();
        }
        expectedModCount = PriorityQueue.access$100(this$0);
    }
    
    final void checkForComodification() {
        if (PriorityQueue.access$100(this$0) != expectedModCount) throw new ConcurrentModificationException();
    }
}
