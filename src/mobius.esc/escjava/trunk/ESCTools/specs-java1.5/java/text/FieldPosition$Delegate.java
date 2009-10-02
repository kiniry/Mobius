package java.text;

class FieldPosition$Delegate implements Format$FieldDelegate {
    
    /*synthetic*/ FieldPosition$Delegate(FieldPosition x0, java.text.FieldPosition$1 x1) {
        this(x0);
    }
    /*synthetic*/ final FieldPosition this$0;
    
    private FieldPosition$Delegate(/*synthetic*/ final FieldPosition this$0) {
        this.this$0 = this$0;
        
    }
    private boolean encounteredField;
    
    public void formatted(Format$Field attr, Object value, int start, int end, StringBuffer buffer) {
        if (!encounteredField && FieldPosition.access$100(this$0, attr)) {
            this$0.setBeginIndex(start);
            this$0.setEndIndex(end);
            encounteredField = (start != end);
        }
    }
    
    public void formatted(int fieldID, Format$Field attr, Object value, int start, int end, StringBuffer buffer) {
        if (!encounteredField && FieldPosition.access$200(this$0, attr, fieldID)) {
            this$0.setBeginIndex(start);
            this$0.setEndIndex(end);
            encounteredField = (start != end);
        }
    }
}
