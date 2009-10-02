package java.awt.event;

import java.awt.Component;
import java.awt.GraphicsEnvironment;
import java.awt.Toolkit;
import java.io.IOException;
import java.io.ObjectInputStream;

public class KeyEvent extends InputEvent {
    private boolean isProxyActive = false;
    public static final int KEY_FIRST = 400;
    public static final int KEY_LAST = 402;
    public static final int KEY_TYPED = KEY_FIRST;
    public static final int KEY_PRESSED = 1 + KEY_FIRST;
    public static final int KEY_RELEASED = 2 + KEY_FIRST;
    public static final int VK_ENTER = '\n';
    public static final int VK_BACK_SPACE = '\b';
    public static final int VK_TAB = '\t';
    public static final int VK_CANCEL = 3;
    public static final int VK_CLEAR = 12;
    public static final int VK_SHIFT = 16;
    public static final int VK_CONTROL = 17;
    public static final int VK_ALT = 18;
    public static final int VK_PAUSE = 19;
    public static final int VK_CAPS_LOCK = 20;
    public static final int VK_ESCAPE = 27;
    public static final int VK_SPACE = 32;
    public static final int VK_PAGE_UP = 33;
    public static final int VK_PAGE_DOWN = 34;
    public static final int VK_END = 35;
    public static final int VK_HOME = 36;
    public static final int VK_LEFT = 37;
    public static final int VK_UP = 38;
    public static final int VK_RIGHT = 39;
    public static final int VK_DOWN = 40;
    public static final int VK_COMMA = 44;
    public static final int VK_MINUS = 45;
    public static final int VK_PERIOD = 46;
    public static final int VK_SLASH = 47;
    public static final int VK_0 = 48;
    public static final int VK_1 = 49;
    public static final int VK_2 = 50;
    public static final int VK_3 = 51;
    public static final int VK_4 = 52;
    public static final int VK_5 = 53;
    public static final int VK_6 = 54;
    public static final int VK_7 = 55;
    public static final int VK_8 = 56;
    public static final int VK_9 = 57;
    public static final int VK_SEMICOLON = 59;
    public static final int VK_EQUALS = 61;
    public static final int VK_A = 65;
    public static final int VK_B = 66;
    public static final int VK_C = 67;
    public static final int VK_D = 68;
    public static final int VK_E = 69;
    public static final int VK_F = 70;
    public static final int VK_G = 71;
    public static final int VK_H = 72;
    public static final int VK_I = 73;
    public static final int VK_J = 74;
    public static final int VK_K = 75;
    public static final int VK_L = 76;
    public static final int VK_M = 77;
    public static final int VK_N = 78;
    public static final int VK_O = 79;
    public static final int VK_P = 80;
    public static final int VK_Q = 81;
    public static final int VK_R = 82;
    public static final int VK_S = 83;
    public static final int VK_T = 84;
    public static final int VK_U = 85;
    public static final int VK_V = 86;
    public static final int VK_W = 87;
    public static final int VK_X = 88;
    public static final int VK_Y = 89;
    public static final int VK_Z = 90;
    public static final int VK_OPEN_BRACKET = 91;
    public static final int VK_BACK_SLASH = 92;
    public static final int VK_CLOSE_BRACKET = 93;
    public static final int VK_NUMPAD0 = 96;
    public static final int VK_NUMPAD1 = 97;
    public static final int VK_NUMPAD2 = 98;
    public static final int VK_NUMPAD3 = 99;
    public static final int VK_NUMPAD4 = 100;
    public static final int VK_NUMPAD5 = 101;
    public static final int VK_NUMPAD6 = 102;
    public static final int VK_NUMPAD7 = 103;
    public static final int VK_NUMPAD8 = 104;
    public static final int VK_NUMPAD9 = 105;
    public static final int VK_MULTIPLY = 106;
    public static final int VK_ADD = 107;
    public static final int VK_SEPARATER = 108;
    public static final int VK_SEPARATOR = VK_SEPARATER;
    public static final int VK_SUBTRACT = 109;
    public static final int VK_DECIMAL = 110;
    public static final int VK_DIVIDE = 111;
    public static final int VK_DELETE = 127;
    public static final int VK_NUM_LOCK = 144;
    public static final int VK_SCROLL_LOCK = 145;
    public static final int VK_F1 = 112;
    public static final int VK_F2 = 113;
    public static final int VK_F3 = 114;
    public static final int VK_F4 = 115;
    public static final int VK_F5 = 116;
    public static final int VK_F6 = 117;
    public static final int VK_F7 = 118;
    public static final int VK_F8 = 119;
    public static final int VK_F9 = 120;
    public static final int VK_F10 = 121;
    public static final int VK_F11 = 122;
    public static final int VK_F12 = 123;
    public static final int VK_F13 = 61440;
    public static final int VK_F14 = 61441;
    public static final int VK_F15 = 61442;
    public static final int VK_F16 = 61443;
    public static final int VK_F17 = 61444;
    public static final int VK_F18 = 61445;
    public static final int VK_F19 = 61446;
    public static final int VK_F20 = 61447;
    public static final int VK_F21 = 61448;
    public static final int VK_F22 = 61449;
    public static final int VK_F23 = 61450;
    public static final int VK_F24 = 61451;
    public static final int VK_PRINTSCREEN = 154;
    public static final int VK_INSERT = 155;
    public static final int VK_HELP = 156;
    public static final int VK_META = 157;
    public static final int VK_BACK_QUOTE = 192;
    public static final int VK_QUOTE = 222;
    public static final int VK_KP_UP = 224;
    public static final int VK_KP_DOWN = 225;
    public static final int VK_KP_LEFT = 226;
    public static final int VK_KP_RIGHT = 227;
    public static final int VK_DEAD_GRAVE = 128;
    public static final int VK_DEAD_ACUTE = 129;
    public static final int VK_DEAD_CIRCUMFLEX = 130;
    public static final int VK_DEAD_TILDE = 131;
    public static final int VK_DEAD_MACRON = 132;
    public static final int VK_DEAD_BREVE = 133;
    public static final int VK_DEAD_ABOVEDOT = 134;
    public static final int VK_DEAD_DIAERESIS = 135;
    public static final int VK_DEAD_ABOVERING = 136;
    public static final int VK_DEAD_DOUBLEACUTE = 137;
    public static final int VK_DEAD_CARON = 138;
    public static final int VK_DEAD_CEDILLA = 139;
    public static final int VK_DEAD_OGONEK = 140;
    public static final int VK_DEAD_IOTA = 141;
    public static final int VK_DEAD_VOICED_SOUND = 142;
    public static final int VK_DEAD_SEMIVOICED_SOUND = 143;
    public static final int VK_AMPERSAND = 150;
    public static final int VK_ASTERISK = 151;
    public static final int VK_QUOTEDBL = 152;
    public static final int VK_LESS = 153;
    public static final int VK_GREATER = 160;
    public static final int VK_BRACELEFT = 161;
    public static final int VK_BRACERIGHT = 162;
    public static final int VK_AT = 512;
    public static final int VK_COLON = 513;
    public static final int VK_CIRCUMFLEX = 514;
    public static final int VK_DOLLAR = 515;
    public static final int VK_EURO_SIGN = 516;
    public static final int VK_EXCLAMATION_MARK = 517;
    public static final int VK_INVERTED_EXCLAMATION_MARK = 518;
    public static final int VK_LEFT_PARENTHESIS = 519;
    public static final int VK_NUMBER_SIGN = 520;
    public static final int VK_PLUS = 521;
    public static final int VK_RIGHT_PARENTHESIS = 522;
    public static final int VK_UNDERSCORE = 523;
    public static final int VK_WINDOWS = 524;
    public static final int VK_CONTEXT_MENU = 525;
    public static final int VK_FINAL = 24;
    public static final int VK_CONVERT = 28;
    public static final int VK_NONCONVERT = 29;
    public static final int VK_ACCEPT = 30;
    public static final int VK_MODECHANGE = 31;
    public static final int VK_KANA = 21;
    public static final int VK_KANJI = 25;
    public static final int VK_ALPHANUMERIC = 240;
    public static final int VK_KATAKANA = 241;
    public static final int VK_HIRAGANA = 242;
    public static final int VK_FULL_WIDTH = 243;
    public static final int VK_HALF_WIDTH = 244;
    public static final int VK_ROMAN_CHARACTERS = 245;
    public static final int VK_ALL_CANDIDATES = 256;
    public static final int VK_PREVIOUS_CANDIDATE = 257;
    public static final int VK_CODE_INPUT = 258;
    public static final int VK_JAPANESE_KATAKANA = 259;
    public static final int VK_JAPANESE_HIRAGANA = 260;
    public static final int VK_JAPANESE_ROMAN = 261;
    public static final int VK_KANA_LOCK = 262;
    public static final int VK_INPUT_METHOD_ON_OFF = 263;
    public static final int VK_CUT = 65489;
    public static final int VK_COPY = 65485;
    public static final int VK_PASTE = 65487;
    public static final int VK_UNDO = 65483;
    public static final int VK_AGAIN = 65481;
    public static final int VK_FIND = 65488;
    public static final int VK_PROPS = 65482;
    public static final int VK_STOP = 65480;
    public static final int VK_COMPOSE = 65312;
    public static final int VK_ALT_GRAPH = 65406;
    public static final int VK_BEGIN = 65368;
    public static final int VK_UNDEFINED = 0;
    public static final char CHAR_UNDEFINED = 65535;
    public static final int KEY_LOCATION_UNKNOWN = 0;
    public static final int KEY_LOCATION_STANDARD = 1;
    public static final int KEY_LOCATION_LEFT = 2;
    public static final int KEY_LOCATION_RIGHT = 3;
    public static final int KEY_LOCATION_NUMPAD = 4;
    int keyCode;
    char keyChar;
    int keyLocation;
    private transient long rawCode = 0;
    private transient long primaryLevelUnicode = 0;
    private transient long primaryLevelKeysym = 0;
    private transient long scancode = 0;
    private static final long serialVersionUID = -2352130953028126954L;
    static {
        NativeLibLoader.loadLibraries();
        if (!GraphicsEnvironment.isHeadless()) {
            initIDs();
        }
    }
    
    private static native void initIDs();
    
    private KeyEvent(Component source, int id, long when, int modifiers, int keyCode, char keyChar, int keyLocation, boolean isProxyActive) {
        this(source, id, when, modifiers, keyCode, keyChar, keyLocation);
        this.isProxyActive = isProxyActive;
    }
    
    public KeyEvent(Component source, int id, long when, int modifiers, int keyCode, char keyChar, int keyLocation) {
        super(source, id, when, modifiers);
        if (id == KEY_TYPED) {
            if (keyChar == CHAR_UNDEFINED) {
                throw new IllegalArgumentException("invalid keyChar");
            }
            if (keyCode != VK_UNDEFINED) {
                throw new IllegalArgumentException("invalid keyCode");
            }
            if (keyLocation != KEY_LOCATION_UNKNOWN) {
                throw new IllegalArgumentException("invalid keyLocation");
            }
        }
        this.keyCode = keyCode;
        this.keyChar = keyChar;
        if ((keyLocation < KEY_LOCATION_UNKNOWN) || (keyLocation > KEY_LOCATION_NUMPAD)) {
            throw new IllegalArgumentException("invalid keyLocation");
        }
        this.keyLocation = keyLocation;
        if ((getModifiers() != 0) && (getModifiersEx() == 0)) {
            setNewModifiers();
        } else if ((getModifiers() == 0) && (getModifiersEx() != 0)) {
            setOldModifiers();
        }
    }
    
    public KeyEvent(Component source, int id, long when, int modifiers, int keyCode, char keyChar) {
        this(source, id, when, modifiers, keyCode, keyChar, KEY_LOCATION_UNKNOWN);
    }
    
    
    public KeyEvent(Component source, int id, long when, int modifiers, int keyCode) {
        this(source, id, when, modifiers, keyCode, (char)keyCode);
    }
    
    public int getKeyCode() {
        return keyCode;
    }
    
    public void setKeyCode(int keyCode) {
        this.keyCode = keyCode;
    }
    
    public char getKeyChar() {
        return keyChar;
    }
    
    public void setKeyChar(char keyChar) {
        this.keyChar = keyChar;
    }
    
    
    public void setModifiers(int modifiers) {
        this.modifiers = modifiers;
        if ((getModifiers() != 0) && (getModifiersEx() == 0)) {
            setNewModifiers();
        } else if ((getModifiers() == 0) && (getModifiersEx() != 0)) {
            setOldModifiers();
        }
    }
    
    public int getKeyLocation() {
        return keyLocation;
    }
    
    public static String getKeyText(int keyCode) {
        if (keyCode >= VK_0 && keyCode <= VK_9 || keyCode >= VK_A && keyCode <= VK_Z) {
            return String.valueOf((char)keyCode);
        }
        switch (keyCode) {
        case VK_ENTER: 
            return Toolkit.getProperty("AWT.enter", "Enter");
        
        case VK_BACK_SPACE: 
            return Toolkit.getProperty("AWT.backSpace", "Backspace");
        
        case VK_TAB: 
            return Toolkit.getProperty("AWT.tab", "Tab");
        
        case VK_CANCEL: 
            return Toolkit.getProperty("AWT.cancel", "Cancel");
        
        case VK_CLEAR: 
            return Toolkit.getProperty("AWT.clear", "Clear");
        
        case VK_COMPOSE: 
            return Toolkit.getProperty("AWT.compose", "Compose");
        
        case VK_PAUSE: 
            return Toolkit.getProperty("AWT.pause", "Pause");
        
        case VK_CAPS_LOCK: 
            return Toolkit.getProperty("AWT.capsLock", "Caps Lock");
        
        case VK_ESCAPE: 
            return Toolkit.getProperty("AWT.escape", "Escape");
        
        case VK_SPACE: 
            return Toolkit.getProperty("AWT.space", "Space");
        
        case VK_PAGE_UP: 
            return Toolkit.getProperty("AWT.pgup", "Page Up");
        
        case VK_PAGE_DOWN: 
            return Toolkit.getProperty("AWT.pgdn", "Page Down");
        
        case VK_END: 
            return Toolkit.getProperty("AWT.end", "End");
        
        case VK_HOME: 
            return Toolkit.getProperty("AWT.home", "Home");
        
        case VK_LEFT: 
            return Toolkit.getProperty("AWT.left", "Left");
        
        case VK_UP: 
            return Toolkit.getProperty("AWT.up", "Up");
        
        case VK_RIGHT: 
            return Toolkit.getProperty("AWT.right", "Right");
        
        case VK_DOWN: 
            return Toolkit.getProperty("AWT.down", "Down");
        
        case VK_BEGIN: 
            return Toolkit.getProperty("AWT.begin", "Begin");
        
        case VK_SHIFT: 
            return Toolkit.getProperty("AWT.shift", "Shift");
        
        case VK_CONTROL: 
            return Toolkit.getProperty("AWT.control", "Control");
        
        case VK_ALT: 
            return Toolkit.getProperty("AWT.alt", "Alt");
        
        case VK_META: 
            return Toolkit.getProperty("AWT.meta", "Meta");
        
        case VK_ALT_GRAPH: 
            return Toolkit.getProperty("AWT.altGraph", "Alt Graph");
        
        case VK_COMMA: 
            return Toolkit.getProperty("AWT.comma", "Comma");
        
        case VK_PERIOD: 
            return Toolkit.getProperty("AWT.period", "Period");
        
        case VK_SLASH: 
            return Toolkit.getProperty("AWT.slash", "Slash");
        
        case VK_SEMICOLON: 
            return Toolkit.getProperty("AWT.semicolon", "Semicolon");
        
        case VK_EQUALS: 
            return Toolkit.getProperty("AWT.equals", "Equals");
        
        case VK_OPEN_BRACKET: 
            return Toolkit.getProperty("AWT.openBracket", "Open Bracket");
        
        case VK_BACK_SLASH: 
            return Toolkit.getProperty("AWT.backSlash", "Back Slash");
        
        case VK_CLOSE_BRACKET: 
            return Toolkit.getProperty("AWT.closeBracket", "Close Bracket");
        
        case VK_MULTIPLY: 
            return Toolkit.getProperty("AWT.multiply", "NumPad *");
        
        case VK_ADD: 
            return Toolkit.getProperty("AWT.add", "NumPad +");
        
        case VK_SEPARATOR: 
            return Toolkit.getProperty("AWT.separator", "NumPad ,");
        
        case VK_SUBTRACT: 
            return Toolkit.getProperty("AWT.subtract", "NumPad -");
        
        case VK_DECIMAL: 
            return Toolkit.getProperty("AWT.decimal", "NumPad .");
        
        case VK_DIVIDE: 
            return Toolkit.getProperty("AWT.divide", "NumPad /");
        
        case VK_DELETE: 
            return Toolkit.getProperty("AWT.delete", "Delete");
        
        case VK_NUM_LOCK: 
            return Toolkit.getProperty("AWT.numLock", "Num Lock");
        
        case VK_SCROLL_LOCK: 
            return Toolkit.getProperty("AWT.scrollLock", "Scroll Lock");
        
        case VK_WINDOWS: 
            return Toolkit.getProperty("AWT.windows", "Windows");
        
        case VK_CONTEXT_MENU: 
            return Toolkit.getProperty("AWT.context", "Context Menu");
        
        case VK_F1: 
            return Toolkit.getProperty("AWT.f1", "F1");
        
        case VK_F2: 
            return Toolkit.getProperty("AWT.f2", "F2");
        
        case VK_F3: 
            return Toolkit.getProperty("AWT.f3", "F3");
        
        case VK_F4: 
            return Toolkit.getProperty("AWT.f4", "F4");
        
        case VK_F5: 
            return Toolkit.getProperty("AWT.f5", "F5");
        
        case VK_F6: 
            return Toolkit.getProperty("AWT.f6", "F6");
        
        case VK_F7: 
            return Toolkit.getProperty("AWT.f7", "F7");
        
        case VK_F8: 
            return Toolkit.getProperty("AWT.f8", "F8");
        
        case VK_F9: 
            return Toolkit.getProperty("AWT.f9", "F9");
        
        case VK_F10: 
            return Toolkit.getProperty("AWT.f10", "F10");
        
        case VK_F11: 
            return Toolkit.getProperty("AWT.f11", "F11");
        
        case VK_F12: 
            return Toolkit.getProperty("AWT.f12", "F12");
        
        case VK_F13: 
            return Toolkit.getProperty("AWT.f13", "F13");
        
        case VK_F14: 
            return Toolkit.getProperty("AWT.f14", "F14");
        
        case VK_F15: 
            return Toolkit.getProperty("AWT.f15", "F15");
        
        case VK_F16: 
            return Toolkit.getProperty("AWT.f16", "F16");
        
        case VK_F17: 
            return Toolkit.getProperty("AWT.f17", "F17");
        
        case VK_F18: 
            return Toolkit.getProperty("AWT.f18", "F18");
        
        case VK_F19: 
            return Toolkit.getProperty("AWT.f19", "F19");
        
        case VK_F20: 
            return Toolkit.getProperty("AWT.f20", "F20");
        
        case VK_F21: 
            return Toolkit.getProperty("AWT.f21", "F21");
        
        case VK_F22: 
            return Toolkit.getProperty("AWT.f22", "F22");
        
        case VK_F23: 
            return Toolkit.getProperty("AWT.f23", "F23");
        
        case VK_F24: 
            return Toolkit.getProperty("AWT.f24", "F24");
        
        case VK_PRINTSCREEN: 
            return Toolkit.getProperty("AWT.printScreen", "Print Screen");
        
        case VK_INSERT: 
            return Toolkit.getProperty("AWT.insert", "Insert");
        
        case VK_HELP: 
            return Toolkit.getProperty("AWT.help", "Help");
        
        case VK_BACK_QUOTE: 
            return Toolkit.getProperty("AWT.backQuote", "Back Quote");
        
        case VK_QUOTE: 
            return Toolkit.getProperty("AWT.quote", "Quote");
        
        case VK_KP_UP: 
            return Toolkit.getProperty("AWT.up", "Up");
        
        case VK_KP_DOWN: 
            return Toolkit.getProperty("AWT.down", "Down");
        
        case VK_KP_LEFT: 
            return Toolkit.getProperty("AWT.left", "Left");
        
        case VK_KP_RIGHT: 
            return Toolkit.getProperty("AWT.right", "Right");
        
        case VK_DEAD_GRAVE: 
            return Toolkit.getProperty("AWT.deadGrave", "Dead Grave");
        
        case VK_DEAD_ACUTE: 
            return Toolkit.getProperty("AWT.deadAcute", "Dead Acute");
        
        case VK_DEAD_CIRCUMFLEX: 
            return Toolkit.getProperty("AWT.deadCircumflex", "Dead Circumflex");
        
        case VK_DEAD_TILDE: 
            return Toolkit.getProperty("AWT.deadTilde", "Dead Tilde");
        
        case VK_DEAD_MACRON: 
            return Toolkit.getProperty("AWT.deadMacron", "Dead Macron");
        
        case VK_DEAD_BREVE: 
            return Toolkit.getProperty("AWT.deadBreve", "Dead Breve");
        
        case VK_DEAD_ABOVEDOT: 
            return Toolkit.getProperty("AWT.deadAboveDot", "Dead Above Dot");
        
        case VK_DEAD_DIAERESIS: 
            return Toolkit.getProperty("AWT.deadDiaeresis", "Dead Diaeresis");
        
        case VK_DEAD_ABOVERING: 
            return Toolkit.getProperty("AWT.deadAboveRing", "Dead Above Ring");
        
        case VK_DEAD_DOUBLEACUTE: 
            return Toolkit.getProperty("AWT.deadDoubleAcute", "Dead Double Acute");
        
        case VK_DEAD_CARON: 
            return Toolkit.getProperty("AWT.deadCaron", "Dead Caron");
        
        case VK_DEAD_CEDILLA: 
            return Toolkit.getProperty("AWT.deadCedilla", "Dead Cedilla");
        
        case VK_DEAD_OGONEK: 
            return Toolkit.getProperty("AWT.deadOgonek", "Dead Ogonek");
        
        case VK_DEAD_IOTA: 
            return Toolkit.getProperty("AWT.deadIota", "Dead Iota");
        
        case VK_DEAD_VOICED_SOUND: 
            return Toolkit.getProperty("AWT.deadVoicedSound", "Dead Voiced Sound");
        
        case VK_DEAD_SEMIVOICED_SOUND: 
            return Toolkit.getProperty("AWT.deadSemivoicedSound", "Dead Semivoiced Sound");
        
        case VK_AMPERSAND: 
            return Toolkit.getProperty("AWT.ampersand", "Ampersand");
        
        case VK_ASTERISK: 
            return Toolkit.getProperty("AWT.asterisk", "Asterisk");
        
        case VK_QUOTEDBL: 
            return Toolkit.getProperty("AWT.quoteDbl", "Double Quote");
        
        case VK_LESS: 
            return Toolkit.getProperty("AWT.Less", "Less");
        
        case VK_GREATER: 
            return Toolkit.getProperty("AWT.greater", "Greater");
        
        case VK_BRACELEFT: 
            return Toolkit.getProperty("AWT.braceLeft", "Left Brace");
        
        case VK_BRACERIGHT: 
            return Toolkit.getProperty("AWT.braceRight", "Right Brace");
        
        case VK_AT: 
            return Toolkit.getProperty("AWT.at", "At");
        
        case VK_COLON: 
            return Toolkit.getProperty("AWT.colon", "Colon");
        
        case VK_CIRCUMFLEX: 
            return Toolkit.getProperty("AWT.circumflex", "Circumflex");
        
        case VK_DOLLAR: 
            return Toolkit.getProperty("AWT.dollar", "Dollar");
        
        case VK_EURO_SIGN: 
            return Toolkit.getProperty("AWT.euro", "Euro");
        
        case VK_EXCLAMATION_MARK: 
            return Toolkit.getProperty("AWT.exclamationMark", "Exclamation Mark");
        
        case VK_INVERTED_EXCLAMATION_MARK: 
            return Toolkit.getProperty("AWT.invertedExclamationMark", "Inverted Exclamation Mark");
        
        case VK_LEFT_PARENTHESIS: 
            return Toolkit.getProperty("AWT.leftParenthesis", "Left Parenthesis");
        
        case VK_NUMBER_SIGN: 
            return Toolkit.getProperty("AWT.numberSign", "Number Sign");
        
        case VK_MINUS: 
            return Toolkit.getProperty("AWT.minus", "Minus");
        
        case VK_PLUS: 
            return Toolkit.getProperty("AWT.plus", "Plus");
        
        case VK_RIGHT_PARENTHESIS: 
            return Toolkit.getProperty("AWT.rightParenthesis", "Right Parenthesis");
        
        case VK_UNDERSCORE: 
            return Toolkit.getProperty("AWT.underscore", "Underscore");
        
        case VK_FINAL: 
            return Toolkit.getProperty("AWT.final", "Final");
        
        case VK_CONVERT: 
            return Toolkit.getProperty("AWT.convert", "Convert");
        
        case VK_NONCONVERT: 
            return Toolkit.getProperty("AWT.noconvert", "No Convert");
        
        case VK_ACCEPT: 
            return Toolkit.getProperty("AWT.accept", "Accept");
        
        case VK_MODECHANGE: 
            return Toolkit.getProperty("AWT.modechange", "Mode Change");
        
        case VK_KANA: 
            return Toolkit.getProperty("AWT.kana", "Kana");
        
        case VK_KANJI: 
            return Toolkit.getProperty("AWT.kanji", "Kanji");
        
        case VK_ALPHANUMERIC: 
            return Toolkit.getProperty("AWT.alphanumeric", "Alphanumeric");
        
        case VK_KATAKANA: 
            return Toolkit.getProperty("AWT.katakana", "Katakana");
        
        case VK_HIRAGANA: 
            return Toolkit.getProperty("AWT.hiragana", "Hiragana");
        
        case VK_FULL_WIDTH: 
            return Toolkit.getProperty("AWT.fullWidth", "Full-Width");
        
        case VK_HALF_WIDTH: 
            return Toolkit.getProperty("AWT.halfWidth", "Half-Width");
        
        case VK_ROMAN_CHARACTERS: 
            return Toolkit.getProperty("AWT.romanCharacters", "Roman Characters");
        
        case VK_ALL_CANDIDATES: 
            return Toolkit.getProperty("AWT.allCandidates", "All Candidates");
        
        case VK_PREVIOUS_CANDIDATE: 
            return Toolkit.getProperty("AWT.previousCandidate", "Previous Candidate");
        
        case VK_CODE_INPUT: 
            return Toolkit.getProperty("AWT.codeInput", "Code Input");
        
        case VK_JAPANESE_KATAKANA: 
            return Toolkit.getProperty("AWT.japaneseKatakana", "Japanese Katakana");
        
        case VK_JAPANESE_HIRAGANA: 
            return Toolkit.getProperty("AWT.japaneseHiragana", "Japanese Hiragana");
        
        case VK_JAPANESE_ROMAN: 
            return Toolkit.getProperty("AWT.japaneseRoman", "Japanese Roman");
        
        case VK_KANA_LOCK: 
            return Toolkit.getProperty("AWT.kanaLock", "Kana Lock");
        
        case VK_INPUT_METHOD_ON_OFF: 
            return Toolkit.getProperty("AWT.inputMethodOnOff", "Input Method On/Off");
        
        case VK_AGAIN: 
            return Toolkit.getProperty("AWT.again", "Again");
        
        case VK_UNDO: 
            return Toolkit.getProperty("AWT.undo", "Undo");
        
        case VK_COPY: 
            return Toolkit.getProperty("AWT.copy", "Copy");
        
        case VK_PASTE: 
            return Toolkit.getProperty("AWT.paste", "Paste");
        
        case VK_CUT: 
            return Toolkit.getProperty("AWT.cut", "Cut");
        
        case VK_FIND: 
            return Toolkit.getProperty("AWT.find", "Find");
        
        case VK_PROPS: 
            return Toolkit.getProperty("AWT.props", "Props");
        
        case VK_STOP: 
            return Toolkit.getProperty("AWT.stop", "Stop");
        
        }
        if (keyCode >= VK_NUMPAD0 && keyCode <= VK_NUMPAD9) {
            String numpad = Toolkit.getProperty("AWT.numpad", "NumPad");
            char c = (char)(keyCode - VK_NUMPAD0 + '0');
            return numpad + "-" + c;
        }
        String unknown = Toolkit.getProperty("AWT.unknown", "Unknown");
        return unknown + " keyCode: 0x" + Integer.toString(keyCode, 16);
    }
    
    public static String getKeyModifiersText(int modifiers) {
        StringBuffer buf = new StringBuffer();
        if ((modifiers & InputEvent.META_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.meta", "Meta"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.CTRL_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.control", "Ctrl"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.ALT_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.alt", "Alt"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.SHIFT_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.shift", "Shift"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.ALT_GRAPH_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.altGraph", "Alt Graph"));
            buf.append("+");
        }
        if ((modifiers & InputEvent.BUTTON1_MASK) != 0) {
            buf.append(Toolkit.getProperty("AWT.button1", "Button1"));
            buf.append("+");
        }
        if (buf.length() > 0) {
            buf.setLength(buf.length() - 1);
        }
        return buf.toString();
    }
    
    public boolean isActionKey() {
        switch (keyCode) {
        case VK_HOME: 
        
        case VK_END: 
        
        case VK_PAGE_UP: 
        
        case VK_PAGE_DOWN: 
        
        case VK_UP: 
        
        case VK_DOWN: 
        
        case VK_LEFT: 
        
        case VK_RIGHT: 
        
        case VK_BEGIN: 
        
        case VK_KP_LEFT: 
        
        case VK_KP_UP: 
        
        case VK_KP_RIGHT: 
        
        case VK_KP_DOWN: 
        
        case VK_F1: 
        
        case VK_F2: 
        
        case VK_F3: 
        
        case VK_F4: 
        
        case VK_F5: 
        
        case VK_F6: 
        
        case VK_F7: 
        
        case VK_F8: 
        
        case VK_F9: 
        
        case VK_F10: 
        
        case VK_F11: 
        
        case VK_F12: 
        
        case VK_F13: 
        
        case VK_F14: 
        
        case VK_F15: 
        
        case VK_F16: 
        
        case VK_F17: 
        
        case VK_F18: 
        
        case VK_F19: 
        
        case VK_F20: 
        
        case VK_F21: 
        
        case VK_F22: 
        
        case VK_F23: 
        
        case VK_F24: 
        
        case VK_PRINTSCREEN: 
        
        case VK_SCROLL_LOCK: 
        
        case VK_CAPS_LOCK: 
        
        case VK_NUM_LOCK: 
        
        case VK_PAUSE: 
        
        case VK_INSERT: 
        
        case VK_FINAL: 
        
        case VK_CONVERT: 
        
        case VK_NONCONVERT: 
        
        case VK_ACCEPT: 
        
        case VK_MODECHANGE: 
        
        case VK_KANA: 
        
        case VK_KANJI: 
        
        case VK_ALPHANUMERIC: 
        
        case VK_KATAKANA: 
        
        case VK_HIRAGANA: 
        
        case VK_FULL_WIDTH: 
        
        case VK_HALF_WIDTH: 
        
        case VK_ROMAN_CHARACTERS: 
        
        case VK_ALL_CANDIDATES: 
        
        case VK_PREVIOUS_CANDIDATE: 
        
        case VK_CODE_INPUT: 
        
        case VK_JAPANESE_KATAKANA: 
        
        case VK_JAPANESE_HIRAGANA: 
        
        case VK_JAPANESE_ROMAN: 
        
        case VK_KANA_LOCK: 
        
        case VK_INPUT_METHOD_ON_OFF: 
        
        case VK_AGAIN: 
        
        case VK_UNDO: 
        
        case VK_COPY: 
        
        case VK_PASTE: 
        
        case VK_CUT: 
        
        case VK_FIND: 
        
        case VK_PROPS: 
        
        case VK_STOP: 
        
        case VK_HELP: 
        
        case VK_WINDOWS: 
        
        case VK_CONTEXT_MENU: 
            return true;
        
        }
        return false;
    }
    
    public String paramString() {
        StringBuffer str = new StringBuffer(100);
        switch (id) {
        case KEY_PRESSED: 
            str.append("KEY_PRESSED");
            break;
        
        case KEY_RELEASED: 
            str.append("KEY_RELEASED");
            break;
        
        case KEY_TYPED: 
            str.append("KEY_TYPED");
            break;
        
        default: 
            str.append("unknown type");
            break;
        
        }
        str.append(",keyCode=").append(keyCode);
        str.append(",keyText=").append(getKeyText(keyCode));
        str.append(",keyChar=");
        switch (keyChar) {
        case '\b': 
            str.append(getKeyText(VK_BACK_SPACE));
            break;
        
        case '\t': 
            str.append(getKeyText(VK_TAB));
            break;
        
        case '\n': 
            str.append(getKeyText(VK_ENTER));
            break;
        
        case '\030': 
            str.append(getKeyText(VK_CANCEL));
            break;
        
        case '\033': 
            str.append(getKeyText(VK_ESCAPE));
            break;
        
        case '': 
            str.append(getKeyText(VK_DELETE));
            break;
        
        case CHAR_UNDEFINED: 
            str.append(Toolkit.getProperty("AWT.undefined", "Undefined"));
            str.append(" keyChar");
            break;
        
        default: 
            str.append("\'").append(keyChar).append("\'");
            break;
        
        }
        if (getModifiers() != 0) {
            str.append(",modifiers=").append(getKeyModifiersText(modifiers));
        }
        if (getModifiersEx() != 0) {
            str.append(",extModifiers=").append(getModifiersExText(modifiers));
        }
        str.append(",keyLocation=");
        switch (keyLocation) {
        case KEY_LOCATION_UNKNOWN: 
            str.append("KEY_LOCATION_UNKNOWN");
            break;
        
        case KEY_LOCATION_STANDARD: 
            str.append("KEY_LOCATION_STANDARD");
            break;
        
        case KEY_LOCATION_LEFT: 
            str.append("KEY_LOCATION_LEFT");
            break;
        
        case KEY_LOCATION_RIGHT: 
            str.append("KEY_LOCATION_RIGHT");
            break;
        
        case KEY_LOCATION_NUMPAD: 
            str.append("KEY_LOCATION_NUMPAD");
            break;
        
        default: 
            str.append("KEY_LOCATION_UNKNOWN");
            break;
        
        }
        str.append(",rawCode=").append(rawCode);
        str.append(",primaryLevelUnicode=").append(primaryLevelUnicode);
        str.append(",primaryLevelKeysym=").append(primaryLevelKeysym);
        str.append(",scancode=").append(scancode);
        return str.toString();
    }
    
    private void setNewModifiers() {
        if ((modifiers & SHIFT_MASK) != 0) {
            modifiers |= SHIFT_DOWN_MASK;
        }
        if ((modifiers & ALT_MASK) != 0) {
            modifiers |= ALT_DOWN_MASK;
        }
        if ((modifiers & CTRL_MASK) != 0) {
            modifiers |= CTRL_DOWN_MASK;
        }
        if ((modifiers & META_MASK) != 0) {
            modifiers |= META_DOWN_MASK;
        }
        if ((modifiers & ALT_GRAPH_MASK) != 0) {
            modifiers |= ALT_GRAPH_DOWN_MASK;
        }
        if ((modifiers & BUTTON1_MASK) != 0) {
            modifiers |= BUTTON1_DOWN_MASK;
        }
    }
    
    private void setOldModifiers() {
        if ((modifiers & SHIFT_DOWN_MASK) != 0) {
            modifiers |= SHIFT_MASK;
        }
        if ((modifiers & ALT_DOWN_MASK) != 0) {
            modifiers |= ALT_MASK;
        }
        if ((modifiers & CTRL_DOWN_MASK) != 0) {
            modifiers |= CTRL_MASK;
        }
        if ((modifiers & META_DOWN_MASK) != 0) {
            modifiers |= META_MASK;
        }
        if ((modifiers & ALT_GRAPH_DOWN_MASK) != 0) {
            modifiers |= ALT_GRAPH_MASK;
        }
        if ((modifiers & BUTTON1_DOWN_MASK) != 0) {
            modifiers |= BUTTON1_MASK;
        }
    }
    
    private void readObject(ObjectInputStream s) throws IOException, ClassNotFoundException {
        s.defaultReadObject();
        if (getModifiers() != 0 && getModifiersEx() == 0) {
            setNewModifiers();
        }
    }
}
