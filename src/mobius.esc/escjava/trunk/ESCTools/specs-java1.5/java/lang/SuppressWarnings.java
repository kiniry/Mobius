package java.lang;

import java.lang.annotation.*;
import static java.lang.annotation.ElementType.*;

@Target(value = {TYPE, FIELD, METHOD, PARAMETER, CONSTRUCTOR, LOCAL_VARIABLE})
@Retention(value = RetentionPolicy.SOURCE)
public @interface SuppressWarnings {
    
    String[] value();
}
