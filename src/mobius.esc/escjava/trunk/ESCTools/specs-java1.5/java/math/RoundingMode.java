package java.math;

public enum RoundingMode extends Enum<RoundingMode> {
    /*public static final*/ UP /* = new RoundingMode("UP", 0, BigDecimal.ROUND_UP) */,
    /*public static final*/ DOWN /* = new RoundingMode("DOWN", 1, BigDecimal.ROUND_DOWN) */,
    /*public static final*/ CEILING /* = new RoundingMode("CEILING", 2, BigDecimal.ROUND_CEILING) */,
    /*public static final*/ FLOOR /* = new RoundingMode("FLOOR", 3, BigDecimal.ROUND_FLOOR) */,
    /*public static final*/ HALF_UP /* = new RoundingMode("HALF_UP", 4, BigDecimal.ROUND_HALF_UP) */,
    /*public static final*/ HALF_DOWN /* = new RoundingMode("HALF_DOWN", 5, BigDecimal.ROUND_HALF_DOWN) */,
    /*public static final*/ HALF_EVEN /* = new RoundingMode("HALF_EVEN", 6, BigDecimal.ROUND_HALF_EVEN) */,
    /*public static final*/ UNNECESSARY /* = new RoundingMode("UNNECESSARY", 7, BigDecimal.ROUND_UNNECESSARY) */;
    /*synthetic*/ private static final RoundingMode[] $VALUES = new RoundingMode[]{RoundingMode.UP, RoundingMode.DOWN, RoundingMode.CEILING, RoundingMode.FLOOR, RoundingMode.HALF_UP, RoundingMode.HALF_DOWN, RoundingMode.HALF_EVEN, RoundingMode.UNNECESSARY};
    
    public static final RoundingMode[] values() {
        return (RoundingMode[])$VALUES.clone();
    }
    
    public static RoundingMode valueOf(String name) {
        return (RoundingMode)Enum.valueOf(RoundingMode.class, name);
    }
    final int oldMode;
    
    private RoundingMode(/*synthetic*/ String $enum$name, /*synthetic*/ int $enum$ordinal, int oldMode) {
        super($enum$name, $enum$ordinal);
        this.oldMode = oldMode;
    }
    
    public static RoundingMode valueOf(int rm) {
        switch (rm) {
        case BigDecimal.ROUND_UP: 
            return UP;
        
        case BigDecimal.ROUND_DOWN: 
            return DOWN;
        
        case BigDecimal.ROUND_CEILING: 
            return CEILING;
        
        case BigDecimal.ROUND_FLOOR: 
            return FLOOR;
        
        case BigDecimal.ROUND_HALF_UP: 
            return HALF_UP;
        
        case BigDecimal.ROUND_HALF_DOWN: 
            return HALF_DOWN;
        
        case BigDecimal.ROUND_HALF_EVEN: 
            return HALF_EVEN;
        
        case BigDecimal.ROUND_UNNECESSARY: 
            return UNNECESSARY;
        
        default: 
            throw new IllegalArgumentException("argument out of range");
        
        }
    }
}
