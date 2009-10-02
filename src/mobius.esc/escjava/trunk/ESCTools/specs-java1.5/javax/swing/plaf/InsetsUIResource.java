package javax.swing.plaf;

import java.awt.Insets;
import javax.swing.plaf.UIResource;

public class InsetsUIResource extends Insets implements UIResource {
    
    public InsetsUIResource(int top, int left, int bottom, int right) {
        super(top, left, bottom, right);
    }
}
