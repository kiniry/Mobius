package java.text;

class DontCareFieldPosition extends FieldPosition {
    static final FieldPosition INSTANCE = new DontCareFieldPosition();
    private final Format$FieldDelegate noDelegate = new DontCareFieldPosition$1(this);
    
    private DontCareFieldPosition() {
        super(0);
    }
    
    Format$FieldDelegate getFieldDelegate() {
        return noDelegate;
    }
}
