package java.text;

import java.util.Vector;
import sun.text.UCompactIntArray;
import sun.text.IntHashtable;

final class RBCollationTables$BuildAPI {
    
    /*synthetic*/ RBCollationTables$BuildAPI(RBCollationTables x0, java.text.RBCollationTables$1 x1) {
        this(x0);
    }
    /*synthetic*/ final RBCollationTables this$0;
    
    private RBCollationTables$BuildAPI(/*synthetic*/ final RBCollationTables this$0) {
        this.this$0 = this$0;
        
    }
    
    void fillInTables(boolean f2ary, boolean swap, UCompactIntArray map, Vector cTbl, Vector eTbl, IntHashtable cFlgs, short mso, short mto) {
        RBCollationTables.access$102(this$0, f2ary);
        RBCollationTables.access$202(this$0, swap);
        RBCollationTables.access$302(this$0, map);
        RBCollationTables.access$402(this$0, cTbl);
        RBCollationTables.access$502(this$0, eTbl);
        RBCollationTables.access$602(this$0, cFlgs);
        RBCollationTables.access$702(this$0, mso);
        RBCollationTables.access$802(this$0, mto);
    }
}
