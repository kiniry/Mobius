package java.text;

import java.util.Vector;
import sun.text.UCompactIntArray;
import sun.text.IntHashtable;

final class RBCollationTables {
    
    /*synthetic*/ static short access$802(RBCollationTables x0, short x1) {
        return x0.maxTerOrder = x1;
    }
    
    /*synthetic*/ static short access$702(RBCollationTables x0, short x1) {
        return x0.maxSecOrder = x1;
    }
    
    /*synthetic*/ static IntHashtable access$602(RBCollationTables x0, IntHashtable x1) {
        return x0.contractFlags = x1;
    }
    
    /*synthetic*/ static Vector access$502(RBCollationTables x0, Vector x1) {
        return x0.expandTable = x1;
    }
    
    /*synthetic*/ static Vector access$402(RBCollationTables x0, Vector x1) {
        return x0.contractTable = x1;
    }
    
    /*synthetic*/ static UCompactIntArray access$302(RBCollationTables x0, UCompactIntArray x1) {
        return x0.mapping = x1;
    }
    
    /*synthetic*/ static boolean access$202(RBCollationTables x0, boolean x1) {
        return x0.seAsianSwapping = x1;
    }
    
    /*synthetic*/ static boolean access$102(RBCollationTables x0, boolean x1) {
        return x0.frenchSec = x1;
    }
    {
    }
    
    public RBCollationTables(String rules, int decmp) throws ParseException {
        
        this.rules = rules;
        RBTableBuilder builder = new RBTableBuilder(new RBCollationTables$BuildAPI(this, null));
        builder.build(rules, decmp);
    }
    {
    }
    
    public String getRules() {
        return rules;
    }
    
    public boolean isFrenchSec() {
        return frenchSec;
    }
    
    public boolean isSEAsianSwapping() {
        return seAsianSwapping;
    }
    
    Vector getContractValues(int ch) {
        int index = mapping.elementAt(ch);
        return getContractValuesImpl(index - CONTRACTCHARINDEX);
    }
    
    private Vector getContractValuesImpl(int index) {
        if (index >= 0) {
            return (Vector)(Vector)contractTable.elementAt(index);
        } else {
            return null;
        }
    }
    
    boolean usedInContractSeq(int c) {
        return contractFlags.get(c) == 1;
    }
    
    int getMaxExpansion(int order) {
        int result = 1;
        if (expandTable != null) {
            for (int i = 0; i < expandTable.size(); i++) {
                int[] valueList = (int[])(int[])expandTable.elementAt(i);
                int length = valueList.length;
                if (length > result && valueList[length - 1] == order) {
                    result = length;
                }
            }
        }
        return result;
    }
    
    final int[] getExpandValueList(int order) {
        return (int[])(int[])expandTable.elementAt(order - EXPANDCHARINDEX);
    }
    
    int getUnicodeOrder(int ch) {
        return mapping.elementAt(ch);
    }
    
    short getMaxSecOrder() {
        return maxSecOrder;
    }
    
    short getMaxTerOrder() {
        return maxTerOrder;
    }
    
    static void reverse(StringBuffer result, int from, int to) {
        int i = from;
        char swap;
        int j = to - 1;
        while (i < j) {
            swap = result.charAt(i);
            result.setCharAt(i, result.charAt(j));
            result.setCharAt(j, swap);
            i++;
            j--;
        }
    }
    
    static final int getEntry(Vector list, String name, boolean fwd) {
        for (int i = 0; i < list.size(); i++) {
            EntryPair pair = (EntryPair)(EntryPair)list.elementAt(i);
            if (pair.fwd == fwd && pair.entryName.equals(name)) {
                return i;
            }
        }
        return UNMAPPED;
    }
    static final int EXPANDCHARINDEX = 2113929216;
    static final int CONTRACTCHARINDEX = 2130706432;
    static final int UNMAPPED = -1;
    static final int PRIMARYORDERMASK = -65536;
    static final int SECONDARYORDERMASK = 65280;
    static final int TERTIARYORDERMASK = 255;
    static final int PRIMARYDIFFERENCEONLY = -65536;
    static final int SECONDARYDIFFERENCEONLY = -256;
    static final int PRIMARYORDERSHIFT = 16;
    static final int SECONDARYORDERSHIFT = 8;
    private String rules = null;
    private boolean frenchSec = false;
    private boolean seAsianSwapping = false;
    private UCompactIntArray mapping = null;
    private Vector contractTable = null;
    private Vector expandTable = null;
    private IntHashtable contractFlags = null;
    private short maxSecOrder = 0;
    private short maxTerOrder = 0;
}
