package javax.swing.text;

class ElementIterator$StackItem implements Cloneable {
    
    /*synthetic*/ static void access$300(ElementIterator$StackItem x0) {
        x0.incrementIndex();
    }
    
    /*synthetic*/ static int access$200(ElementIterator$StackItem x0) {
        return x0.getIndex();
    }
    
    /*synthetic*/ static Element access$100(ElementIterator$StackItem x0) {
        return x0.getElement();
    }
    
    /*synthetic*/ ElementIterator$StackItem(ElementIterator x0, Element x1, javax.swing.text.ElementIterator$1 x2) {
        this(x0, x1);
    }
    /*synthetic*/ final ElementIterator this$0;
    Element item;
    int childIndex;
    
    private ElementIterator$StackItem(/*synthetic*/ final ElementIterator this$0, Element elem) {
        this.this$0 = this$0;
        
        this.item = elem;
        this.childIndex = -1;
    }
    
    private void incrementIndex() {
        childIndex++;
    }
    
    private Element getElement() {
        return item;
    }
    
    private int getIndex() {
        return childIndex;
    }
    
    protected Object clone() throws java.lang.CloneNotSupportedException {
        return super.clone();
    }
}
