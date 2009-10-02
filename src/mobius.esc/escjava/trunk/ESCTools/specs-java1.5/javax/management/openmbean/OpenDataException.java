package javax.management.openmbean;

import java.io.Serializable;
import javax.management.JMException;

public class OpenDataException extends JMException implements Serializable {
    private static final long serialVersionUID = 8346311255433349870L;
    
    public OpenDataException() {
        
    }
    
    public OpenDataException(String msg) {
        super(msg);
    }
}
