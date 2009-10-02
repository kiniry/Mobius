package java.awt;

import java.security.BasicPermission;

public final class AWTPermission extends BasicPermission {
    private static final long serialVersionUID = 8890392402588814465L;
    
    public AWTPermission(String name) {
        super(name);
    }
    
    public AWTPermission(String name, String actions) {
        super(name, actions);
    }
}
