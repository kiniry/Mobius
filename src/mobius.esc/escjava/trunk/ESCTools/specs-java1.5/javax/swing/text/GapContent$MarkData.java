package javax.swing.text;

import java.lang.ref.WeakReference;
import java.lang.ref.ReferenceQueue;

final class GapContent$MarkData extends WeakReference {
    /*synthetic*/ final GapContent this$0;
    
    GapContent$MarkData(/*synthetic*/ final GapContent this$0, int index) {
        super(null);
        this.this$0 = this$0;
        this.index = index;
    }
    
    GapContent$MarkData(/*synthetic*/ final GapContent this$0, int index, GapContent$StickyPosition position, ReferenceQueue queue) {
        super(position, queue);
        this.this$0 = this$0;
        this.index = index;
    }
    
    public final int getOffset() {
        int g0 = this$0.getGapStart();
        int g1 = this$0.getGapEnd();
        int offs = (index < g0) ? index : index - (g1 - g0);
        return Math.max(offs, 0);
    }
    
    GapContent$StickyPosition getPosition() {
        return (GapContent$StickyPosition)(GapContent$StickyPosition)get();
    }
    int index;
}
