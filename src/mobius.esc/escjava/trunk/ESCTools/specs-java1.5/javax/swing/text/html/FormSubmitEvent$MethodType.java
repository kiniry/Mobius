package javax.swing.text.html;

import javax.swing.text.*;

public class FormSubmitEvent$MethodType extends Enum {
    public static final FormSubmitEvent$MethodType GET  = new FormSubmitEvent$MethodType("GET", 0);
    public static final FormSubmitEvent$MethodType POST  = new FormSubmitEvent$MethodType("POST", 1);
    /*synthetic*/ private static final FormSubmitEvent$MethodType[] $VALUES = new FormSubmitEvent$MethodType[]{FormSubmitEvent$MethodType.GET, FormSubmitEvent$MethodType.POST};
    
    public static final FormSubmitEvent$MethodType[] values() {
        return (FormSubmitEvent$MethodType[])$VALUES.clone();
    }
    
    public static FormSubmitEvent$MethodType valueOf(String name) {
        return (FormSubmitEvent$MethodType)Enum.valueOf(FormSubmitEvent.MethodType.class, name);
    }
    
    private FormSubmitEvent$MethodType(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
