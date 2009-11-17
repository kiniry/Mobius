package javax.swing.plaf;

import java.awt.Dimension;
import javax.swing.plaf.UIResource;

public class DimensionUIResource extends Dimension implements UIResource {
    
    public DimensionUIResource(int width, int height) {
        super(width, height);
    }
}
