package java.lang;

import java.lang.annotation.*;

@Target(value = ElementType.METHOD)
@Retention(value = RetentionPolicy.SOURCE)
public @interface Override {
}
