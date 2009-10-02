package javax.swing.text;

class GapContent$MarkVector extends GapVector {
    
    GapContent$MarkVector() {
        
    }
    
    GapContent$MarkVector(int size) {
        super(size);
    }
    
    protected Object allocateArray(int len) {
        return new GapContent$MarkData[len];
    }
    
    protected int getArrayLength() {
        GapContent$MarkData[] marks = (GapContent$MarkData[])(GapContent$MarkData[])getArray();
        return marks.length;
    }
    
    public int size() {
        int len = getArrayLength() - (getGapEnd() - getGapStart());
        return len;
    }
    
    public void insertElementAt(GapContent$MarkData m, int index) {
        oneMark[0] = m;
        replace(index, 0, oneMark, 1);
    }
    
    public void addElement(GapContent$MarkData m) {
        insertElementAt(m, size());
    }
    
    public GapContent$MarkData elementAt(int index) {
        int g0 = getGapStart();
        int g1 = getGapEnd();
        GapContent$MarkData[] array = (GapContent$MarkData[])(GapContent$MarkData[])getArray();
        if (index < g0) {
            return array[index];
        } else {
            index += g1 - g0;
            return array[index];
        }
    }
    
    protected void replaceRange(int start, int end, Object[] marks) {
        int g0 = getGapStart();
        int g1 = getGapEnd();
        int index = start;
        int newIndex = 0;
        Object[] array = (Object[])(Object[])getArray();
        if (start >= g0) {
            index += (g1 - g0);
            end += (g1 - g0);
        } else if (end >= g0) {
            end += (g1 - g0);
            while (index < g0) {
                array[index++] = marks[newIndex++];
            }
            index = g1;
        } else {
            while (index < end) {
                array[index++] = marks[newIndex++];
            }
        }
        while (index < end) {
            array[index++] = marks[newIndex++];
        }
    }
    GapContent$MarkData[] oneMark = new GapContent$MarkData[1];
}
