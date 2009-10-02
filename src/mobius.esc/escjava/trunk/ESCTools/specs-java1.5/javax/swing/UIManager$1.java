package javax.swing;

import java.io.File;
import java.io.FileInputStream;
import java.util.Properties;

class UIManager$1 implements java.security.PrivilegedAction {
    /*synthetic*/ final Properties val$props;
    
    UIManager$1(/*synthetic*/ final Properties val$props) {
        this.val$props = val$props;
        
    }
    
    public Object run() {
        try {
            File file = new File(UIManager.access$100());
            if (file.exists()) {
                FileInputStream ins = new FileInputStream(file);
                val$props.load(ins);
                ins.close();
            }
        } catch (Exception e) {
        }
        UIManager.access$200(val$props, "swing.defaultlaf");
        UIManager.access$200(val$props, "swing.auxiliarylaf");
        UIManager.access$200(val$props, "swing.plaf.multiplexinglaf");
        UIManager.access$200(val$props, "swing.installedlafs");
        UIManager.access$200(val$props, "swing.disablenavaids");
        return null;
    }
}
