package javax.swing.text;

final class GapContent$StickyPosition implements Position {
    /*synthetic*/ final GapContent this$0;
    
    GapContent$StickyPosition(/*synthetic*/ final GapContent this$0) {
        this.this$0 = this$0;
        
    }
    
    void setMark(GapContent$MarkData mark) {
        this.mark = mark;
    }
    
    public final int getOffset() {
        return mark.getOffset();
    }
    
    public String toString() {
        return Integer.toString(getOffset());
    }
    GapContent$MarkData mark;
}
