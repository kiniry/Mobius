package java.util;

public class Formatter$BigDecimalLayoutForm extends Enum {
    public static final Formatter$BigDecimalLayoutForm SCIENTIFIC  = new Formatter$BigDecimalLayoutForm("SCIENTIFIC", 0) ;
    public static final Formatter$BigDecimalLayoutForm DECIMAL_FLOAT  = new Formatter$BigDecimalLayoutForm("DECIMAL_FLOAT", 1) ;
    /*synthetic*/ private static final Formatter$BigDecimalLayoutForm[] $VALUES = new Formatter$BigDecimalLayoutForm[]{Formatter$BigDecimalLayoutForm.SCIENTIFIC, Formatter$BigDecimalLayoutForm.DECIMAL_FLOAT};
    
    public static final Formatter$BigDecimalLayoutForm[] values() {
        return (Formatter$BigDecimalLayoutForm[])$VALUES.clone();
    }
    
    public static Formatter$BigDecimalLayoutForm valueOf(String name) {
        return (Formatter$BigDecimalLayoutForm)Enum.valueOf(Formatter.BigDecimalLayoutForm.class, name);
    }
    
    private Formatter$BigDecimalLayoutForm(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
