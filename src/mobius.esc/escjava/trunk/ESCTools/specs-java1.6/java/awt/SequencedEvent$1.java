package java.awt;

class SequencedEvent$1 implements Conditional {
    /*synthetic*/ final SequencedEvent this$0;
    
    SequencedEvent$1(/*synthetic*/ final SequencedEvent this$0) {
        this.this$0 = this$0;
        
    }
    
    public boolean evaluate() {
        return !this$0.isFirstOrDisposed();
    }
}
