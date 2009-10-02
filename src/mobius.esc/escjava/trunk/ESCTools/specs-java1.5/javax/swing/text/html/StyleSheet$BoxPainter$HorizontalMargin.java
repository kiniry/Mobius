package javax.swing.text.html;

import java.util.*;
import java.awt.*;
import java.io.*;
import java.net.*;
import javax.swing.border.*;
import javax.swing.text.*;

enum StyleSheet$BoxPainter$HorizontalMargin extends Enum<StyleSheet$BoxPainter$HorizontalMargin> {
    /*public static final*/ LEFT /* = new StyleSheet$BoxPainter$HorizontalMargin("LEFT", 0) */,
    /*public static final*/ RIGHT /* = new StyleSheet$BoxPainter$HorizontalMargin("RIGHT", 1) */;
    /*synthetic*/ private static final StyleSheet$BoxPainter$HorizontalMargin[] $VALUES = new StyleSheet$BoxPainter$HorizontalMargin[]{StyleSheet$BoxPainter$HorizontalMargin.LEFT, StyleSheet$BoxPainter$HorizontalMargin.RIGHT};
    
    public static final StyleSheet$BoxPainter$HorizontalMargin[] values() {
        return (StyleSheet$BoxPainter$HorizontalMargin[])$VALUES.clone();
    }
    
    public static StyleSheet$BoxPainter$HorizontalMargin valueOf(String name) {
        return (StyleSheet$BoxPainter$HorizontalMargin)Enum.valueOf(StyleSheet.BoxPainter.HorizontalMargin.class, name);
    }
    
    private StyleSheet$BoxPainter$HorizontalMargin(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal) {
        super($enum$name, $enum$ordinal);
    }
}
