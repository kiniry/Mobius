package java.awt;

import java.util.HashMap;
import java.util.Map;

class VKCollection {
    /*synthetic*/ static final boolean $assertionsDisabled = !VKCollection.class.desiredAssertionStatus();
    Map code2name;
    Map name2code;
    
    public VKCollection() {
        
        code2name = new HashMap();
        name2code = new HashMap();
    }
    
    public synchronized void put(String name, Integer code) {
        if (!$assertionsDisabled && !((name != null) && (code != null))) throw new AssertionError();
        if (!$assertionsDisabled && !(findName(code) == null)) throw new AssertionError();
        if (!$assertionsDisabled && !(findCode(name) == null)) throw new AssertionError();
        code2name.put(code, name);
        name2code.put(name, code);
    }
    
    public synchronized Integer findCode(String name) {
        if (!$assertionsDisabled && !(name != null)) throw new AssertionError();
        return (Integer)(Integer)name2code.get(name);
    }
    
    public synchronized String findName(Integer code) {
        if (!$assertionsDisabled && !(code != null)) throw new AssertionError();
        return (String)(String)code2name.get(code);
    }
}
