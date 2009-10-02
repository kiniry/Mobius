package javax.swing.text;

final class GapContent$UndoPosRef {
    /*synthetic*/ final GapContent this$0;
    
    GapContent$UndoPosRef(/*synthetic*/ final GapContent this$0, GapContent$MarkData rec) {
        this.this$0 = this$0;
        
        this.rec = rec;
        this.undoLocation = rec.getOffset();
    }
    
    protected void resetLocation(int endOffset, int g1) {
        if (undoLocation != endOffset) {
            this.rec.index = undoLocation;
        } else {
            this.rec.index = g1;
        }
    }
    protected int undoLocation;
    protected GapContent$MarkData rec;
}
