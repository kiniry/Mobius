package java.security;

import java.io.*;

public class KeyRep$Type extends Enum {
    public static final  KeyRep$Type SECRET  = new KeyRep$Type("SECRET", 0);
    public static final KeyRep$Type PUBLIC  = new KeyRep$Type("PUBLIC", 1);
    public static final KeyRep$Type PRIVATE  = new KeyRep$Type("PRIVATE", 2) ;
    /*synthetic*/ private static final KeyRep$Type[] $VALUES = new KeyRep$Type[]{KeyRep$Type.SECRET, KeyRep$Type.PUBLIC, KeyRep$Type.PRIVATE};
    
    public static final KeyRep$Type[] values() {
        return (KeyRep$Type[])$VALUES.clone();
    }
    
    public static KeyRep$Type valueOf(String name) {
        return (KeyRep$Type)Enum.valueOf(KeyRep.Type.class, name);
    }
    
    private KeyRep$Type(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
