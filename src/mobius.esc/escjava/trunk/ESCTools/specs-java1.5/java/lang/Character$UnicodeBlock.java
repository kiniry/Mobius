package java.lang;

import java.util.Map;
import java.util.HashMap;
import java.util.Locale;

public final class Character$UnicodeBlock extends Character$Subset {
    private static Map map = new HashMap();
    
    private Character$UnicodeBlock(String idName) {
        super(idName);
        map.put(idName.toUpperCase(Locale.US), this);
    }
    
    private Character$UnicodeBlock(String idName, String alias) {
        this(idName);
        map.put(alias.toUpperCase(Locale.US), this);
    }
    
    private Character$UnicodeBlock(String idName, String[] aliasName) {
        this(idName);
        if (aliasName != null) {
            for (int x = 0; x < aliasName.length; ++x) {
                map.put(aliasName[x].toUpperCase(Locale.US), this);
            }
        }
    }
    public static final Character$UnicodeBlock BASIC_LATIN = new Character$UnicodeBlock("BASIC_LATIN", new String[]{"Basic Latin", "BasicLatin"});
    public static final Character$UnicodeBlock LATIN_1_SUPPLEMENT = new Character$UnicodeBlock("LATIN_1_SUPPLEMENT", new String[]{"Latin-1 Supplement", "Latin-1Supplement"});
    public static final Character$UnicodeBlock LATIN_EXTENDED_A = new Character$UnicodeBlock("LATIN_EXTENDED_A", new String[]{"Latin Extended-A", "LatinExtended-A"});
    public static final Character$UnicodeBlock LATIN_EXTENDED_B = new Character$UnicodeBlock("LATIN_EXTENDED_B", new String[]{"Latin Extended-B", "LatinExtended-B"});
    public static final Character$UnicodeBlock IPA_EXTENSIONS = new Character$UnicodeBlock("IPA_EXTENSIONS", new String[]{"IPA Extensions", "IPAExtensions"});
    public static final Character$UnicodeBlock SPACING_MODIFIER_LETTERS = new Character$UnicodeBlock("SPACING_MODIFIER_LETTERS", new String[]{"Spacing Modifier Letters", "SpacingModifierLetters"});
    public static final Character$UnicodeBlock COMBINING_DIACRITICAL_MARKS = new Character$UnicodeBlock("COMBINING_DIACRITICAL_MARKS", new String[]{"Combining Diacritical Marks", "CombiningDiacriticalMarks"});
    public static final Character$UnicodeBlock GREEK = new Character$UnicodeBlock("GREEK", new String[]{"Greek and Coptic", "GreekandCoptic"});
    public static final Character$UnicodeBlock CYRILLIC = new Character$UnicodeBlock("CYRILLIC");
    public static final Character$UnicodeBlock ARMENIAN = new Character$UnicodeBlock("ARMENIAN");
    public static final Character$UnicodeBlock HEBREW = new Character$UnicodeBlock("HEBREW");
    public static final Character$UnicodeBlock ARABIC = new Character$UnicodeBlock("ARABIC");
    public static final Character$UnicodeBlock DEVANAGARI = new Character$UnicodeBlock("DEVANAGARI");
    public static final Character$UnicodeBlock BENGALI = new Character$UnicodeBlock("BENGALI");
    public static final Character$UnicodeBlock GURMUKHI = new Character$UnicodeBlock("GURMUKHI");
    public static final Character$UnicodeBlock GUJARATI = new Character$UnicodeBlock("GUJARATI");
    public static final Character$UnicodeBlock ORIYA = new Character$UnicodeBlock("ORIYA");
    public static final Character$UnicodeBlock TAMIL = new Character$UnicodeBlock("TAMIL");
    public static final Character$UnicodeBlock TELUGU = new Character$UnicodeBlock("TELUGU");
    public static final Character$UnicodeBlock KANNADA = new Character$UnicodeBlock("KANNADA");
    public static final Character$UnicodeBlock MALAYALAM = new Character$UnicodeBlock("MALAYALAM");
    public static final Character$UnicodeBlock THAI = new Character$UnicodeBlock("THAI");
    public static final Character$UnicodeBlock LAO = new Character$UnicodeBlock("LAO");
    public static final Character$UnicodeBlock TIBETAN = new Character$UnicodeBlock("TIBETAN");
    public static final Character$UnicodeBlock GEORGIAN = new Character$UnicodeBlock("GEORGIAN");
    public static final Character$UnicodeBlock HANGUL_JAMO = new Character$UnicodeBlock("HANGUL_JAMO", new String[]{"Hangul Jamo", "HangulJamo"});
    public static final Character$UnicodeBlock LATIN_EXTENDED_ADDITIONAL = new Character$UnicodeBlock("LATIN_EXTENDED_ADDITIONAL", new String[]{"Latin Extended Additional", "LatinExtendedAdditional"});
    public static final Character$UnicodeBlock GREEK_EXTENDED = new Character$UnicodeBlock("GREEK_EXTENDED", new String[]{"Greek Extended", "GreekExtended"});
    public static final Character$UnicodeBlock GENERAL_PUNCTUATION = new Character$UnicodeBlock("GENERAL_PUNCTUATION", new String[]{"General Punctuation", "GeneralPunctuation"});
    public static final Character$UnicodeBlock SUPERSCRIPTS_AND_SUBSCRIPTS = new Character$UnicodeBlock("SUPERSCRIPTS_AND_SUBSCRIPTS", new String[]{"Superscripts and Subscripts", "SuperscriptsandSubscripts"});
    public static final Character$UnicodeBlock CURRENCY_SYMBOLS = new Character$UnicodeBlock("CURRENCY_SYMBOLS", new String[]{"Currency Symbols", "CurrencySymbols"});
    public static final Character$UnicodeBlock COMBINING_MARKS_FOR_SYMBOLS = new Character$UnicodeBlock("COMBINING_MARKS_FOR_SYMBOLS", new String[]{"Combining Diacritical Marks for Symbols", "CombiningDiacriticalMarksforSymbols", "Combining Marks for Symbols", "CombiningMarksforSymbols"});
    public static final Character$UnicodeBlock LETTERLIKE_SYMBOLS = new Character$UnicodeBlock("LETTERLIKE_SYMBOLS", new String[]{"Letterlike Symbols", "LetterlikeSymbols"});
    public static final Character$UnicodeBlock NUMBER_FORMS = new Character$UnicodeBlock("NUMBER_FORMS", new String[]{"Number Forms", "NumberForms"});
    public static final Character$UnicodeBlock ARROWS = new Character$UnicodeBlock("ARROWS");
    public static final Character$UnicodeBlock MATHEMATICAL_OPERATORS = new Character$UnicodeBlock("MATHEMATICAL_OPERATORS", new String[]{"Mathematical Operators", "MathematicalOperators"});
    public static final Character$UnicodeBlock MISCELLANEOUS_TECHNICAL = new Character$UnicodeBlock("MISCELLANEOUS_TECHNICAL", new String[]{"Miscellaneous Technical", "MiscellaneousTechnical"});
    public static final Character$UnicodeBlock CONTROL_PICTURES = new Character$UnicodeBlock("CONTROL_PICTURES", new String[]{"Control Pictures", "ControlPictures"});
    public static final Character$UnicodeBlock OPTICAL_CHARACTER_RECOGNITION = new Character$UnicodeBlock("OPTICAL_CHARACTER_RECOGNITION", new String[]{"Optical Character Recognition", "OpticalCharacterRecognition"});
    public static final Character$UnicodeBlock ENCLOSED_ALPHANUMERICS = new Character$UnicodeBlock("ENCLOSED_ALPHANUMERICS", new String[]{"Enclosed Alphanumerics", "EnclosedAlphanumerics"});
    public static final Character$UnicodeBlock BOX_DRAWING = new Character$UnicodeBlock("BOX_DRAWING", new String[]{"Box Drawing", "BoxDrawing"});
    public static final Character$UnicodeBlock BLOCK_ELEMENTS = new Character$UnicodeBlock("BLOCK_ELEMENTS", new String[]{"Block Elements", "BlockElements"});
    public static final Character$UnicodeBlock GEOMETRIC_SHAPES = new Character$UnicodeBlock("GEOMETRIC_SHAPES", new String[]{"Geometric Shapes", "GeometricShapes"});
    public static final Character$UnicodeBlock MISCELLANEOUS_SYMBOLS = new Character$UnicodeBlock("MISCELLANEOUS_SYMBOLS", new String[]{"Miscellaneous Symbols", "MiscellaneousSymbols"});
    public static final Character$UnicodeBlock DINGBATS = new Character$UnicodeBlock("DINGBATS");
    public static final Character$UnicodeBlock CJK_SYMBOLS_AND_PUNCTUATION = new Character$UnicodeBlock("CJK_SYMBOLS_AND_PUNCTUATION", new String[]{"CJK Symbols and Punctuation", "CJKSymbolsandPunctuation"});
    public static final Character$UnicodeBlock HIRAGANA = new Character$UnicodeBlock("HIRAGANA");
    public static final Character$UnicodeBlock KATAKANA = new Character$UnicodeBlock("KATAKANA");
    public static final Character$UnicodeBlock BOPOMOFO = new Character$UnicodeBlock("BOPOMOFO");
    public static final Character$UnicodeBlock HANGUL_COMPATIBILITY_JAMO = new Character$UnicodeBlock("HANGUL_COMPATIBILITY_JAMO", new String[]{"Hangul Compatibility Jamo", "HangulCompatibilityJamo"});
    public static final Character$UnicodeBlock KANBUN = new Character$UnicodeBlock("KANBUN");
    public static final Character$UnicodeBlock ENCLOSED_CJK_LETTERS_AND_MONTHS = new Character$UnicodeBlock("ENCLOSED_CJK_LETTERS_AND_MONTHS", new String[]{"Enclosed CJK Letters and Months", "EnclosedCJKLettersandMonths"});
    public static final Character$UnicodeBlock CJK_COMPATIBILITY = new Character$UnicodeBlock("CJK_COMPATIBILITY", new String[]{"CJK Compatibility", "CJKCompatibility"});
    public static final Character$UnicodeBlock CJK_UNIFIED_IDEOGRAPHS = new Character$UnicodeBlock("CJK_UNIFIED_IDEOGRAPHS", new String[]{"CJK Unified Ideographs", "CJKUnifiedIdeographs"});
    public static final Character$UnicodeBlock HANGUL_SYLLABLES = new Character$UnicodeBlock("HANGUL_SYLLABLES", new String[]{"Hangul Syllables", "HangulSyllables"});
    public static final Character$UnicodeBlock PRIVATE_USE_AREA = new Character$UnicodeBlock("PRIVATE_USE_AREA", new String[]{"Private Use Area", "PrivateUseArea"});
    public static final Character$UnicodeBlock CJK_COMPATIBILITY_IDEOGRAPHS = new Character$UnicodeBlock("CJK_COMPATIBILITY_IDEOGRAPHS", new String[]{"CJK Compatibility Ideographs", "CJKCompatibilityIdeographs"});
    public static final Character$UnicodeBlock ALPHABETIC_PRESENTATION_FORMS = new Character$UnicodeBlock("ALPHABETIC_PRESENTATION_FORMS", new String[]{"Alphabetic Presentation Forms", "AlphabeticPresentationForms"});
    public static final Character$UnicodeBlock ARABIC_PRESENTATION_FORMS_A = new Character$UnicodeBlock("ARABIC_PRESENTATION_FORMS_A", new String[]{"Arabic Presentation Forms-A", "ArabicPresentationForms-A"});
    public static final Character$UnicodeBlock COMBINING_HALF_MARKS = new Character$UnicodeBlock("COMBINING_HALF_MARKS", new String[]{"Combining Half Marks", "CombiningHalfMarks"});
    public static final Character$UnicodeBlock CJK_COMPATIBILITY_FORMS = new Character$UnicodeBlock("CJK_COMPATIBILITY_FORMS", new String[]{"CJK Compatibility Forms", "CJKCompatibilityForms"});
    public static final Character$UnicodeBlock SMALL_FORM_VARIANTS = new Character$UnicodeBlock("SMALL_FORM_VARIANTS", new String[]{"Small Form Variants", "SmallFormVariants"});
    public static final Character$UnicodeBlock ARABIC_PRESENTATION_FORMS_B = new Character$UnicodeBlock("ARABIC_PRESENTATION_FORMS_B", new String[]{"Arabic Presentation Forms-B", "ArabicPresentationForms-B"});
    public static final Character$UnicodeBlock HALFWIDTH_AND_FULLWIDTH_FORMS = new Character$UnicodeBlock("HALFWIDTH_AND_FULLWIDTH_FORMS", new String[]{"Halfwidth and Fullwidth Forms", "HalfwidthandFullwidthForms"});
    public static final Character$UnicodeBlock SPECIALS = new Character$UnicodeBlock("SPECIALS");
    
    public static final Character$UnicodeBlock SURROGATES_AREA = new Character$UnicodeBlock("SURROGATES_AREA");
    public static final Character$UnicodeBlock SYRIAC = new Character$UnicodeBlock("SYRIAC");
    public static final Character$UnicodeBlock THAANA = new Character$UnicodeBlock("THAANA");
    public static final Character$UnicodeBlock SINHALA = new Character$UnicodeBlock("SINHALA");
    public static final Character$UnicodeBlock MYANMAR = new Character$UnicodeBlock("MYANMAR");
    public static final Character$UnicodeBlock ETHIOPIC = new Character$UnicodeBlock("ETHIOPIC");
    public static final Character$UnicodeBlock CHEROKEE = new Character$UnicodeBlock("CHEROKEE");
    public static final Character$UnicodeBlock UNIFIED_CANADIAN_ABORIGINAL_SYLLABICS = new Character$UnicodeBlock("UNIFIED_CANADIAN_ABORIGINAL_SYLLABICS", new String[]{"Unified Canadian Aboriginal Syllabics", "UnifiedCanadianAboriginalSyllabics"});
    public static final Character$UnicodeBlock OGHAM = new Character$UnicodeBlock("OGHAM");
    public static final Character$UnicodeBlock RUNIC = new Character$UnicodeBlock("RUNIC");
    public static final Character$UnicodeBlock KHMER = new Character$UnicodeBlock("KHMER");
    public static final Character$UnicodeBlock MONGOLIAN = new Character$UnicodeBlock("MONGOLIAN");
    public static final Character$UnicodeBlock BRAILLE_PATTERNS = new Character$UnicodeBlock("BRAILLE_PATTERNS", new String[]{"Braille Patterns", "BraillePatterns"});
    public static final Character$UnicodeBlock CJK_RADICALS_SUPPLEMENT = new Character$UnicodeBlock("CJK_RADICALS_SUPPLEMENT", new String[]{"CJK Radicals Supplement", "CJKRadicalsSupplement"});
    public static final Character$UnicodeBlock KANGXI_RADICALS = new Character$UnicodeBlock("KANGXI_RADICALS", new String[]{"Kangxi Radicals", "KangxiRadicals"});
    public static final Character$UnicodeBlock IDEOGRAPHIC_DESCRIPTION_CHARACTERS = new Character$UnicodeBlock("IDEOGRAPHIC_DESCRIPTION_CHARACTERS", new String[]{"Ideographic Description Characters", "IdeographicDescriptionCharacters"});
    public static final Character$UnicodeBlock BOPOMOFO_EXTENDED = new Character$UnicodeBlock("BOPOMOFO_EXTENDED", new String[]{"Bopomofo Extended", "BopomofoExtended"});
    public static final Character$UnicodeBlock CJK_UNIFIED_IDEOGRAPHS_EXTENSION_A = new Character$UnicodeBlock("CJK_UNIFIED_IDEOGRAPHS_EXTENSION_A", new String[]{"CJK Unified Ideographs Extension A", "CJKUnifiedIdeographsExtensionA"});
    public static final Character$UnicodeBlock YI_SYLLABLES = new Character$UnicodeBlock("YI_SYLLABLES", new String[]{"Yi Syllables", "YiSyllables"});
    public static final Character$UnicodeBlock YI_RADICALS = new Character$UnicodeBlock("YI_RADICALS", new String[]{"Yi Radicals", "YiRadicals"});
    public static final Character$UnicodeBlock CYRILLIC_SUPPLEMENTARY = new Character$UnicodeBlock("CYRILLIC_SUPPLEMENTARY", new String[]{"Cyrillic Supplementary", "CyrillicSupplementary"});
    public static final Character$UnicodeBlock TAGALOG = new Character$UnicodeBlock("TAGALOG");
    public static final Character$UnicodeBlock HANUNOO = new Character$UnicodeBlock("HANUNOO");
    public static final Character$UnicodeBlock BUHID = new Character$UnicodeBlock("BUHID");
    public static final Character$UnicodeBlock TAGBANWA = new Character$UnicodeBlock("TAGBANWA");
    public static final Character$UnicodeBlock LIMBU = new Character$UnicodeBlock("LIMBU");
    public static final Character$UnicodeBlock TAI_LE = new Character$UnicodeBlock("TAI_LE", new String[]{"Tai Le", "TaiLe"});
    public static final Character$UnicodeBlock KHMER_SYMBOLS = new Character$UnicodeBlock("KHMER_SYMBOLS", new String[]{"Khmer Symbols", "KhmerSymbols"});
    public static final Character$UnicodeBlock PHONETIC_EXTENSIONS = new Character$UnicodeBlock("PHONETIC_EXTENSIONS", new String[]{"Phonetic Extensions", "PhoneticExtensions"});
    public static final Character$UnicodeBlock MISCELLANEOUS_MATHEMATICAL_SYMBOLS_A = new Character$UnicodeBlock("MISCELLANEOUS_MATHEMATICAL_SYMBOLS_A", new String[]{"Miscellaneous Mathematical Symbols-A", "MiscellaneousMathematicalSymbols-A"});
    public static final Character$UnicodeBlock SUPPLEMENTAL_ARROWS_A = new Character$UnicodeBlock("SUPPLEMENTAL_ARROWS_A", new String[]{"Supplemental Arrows-A", "SupplementalArrows-A"});
    public static final Character$UnicodeBlock SUPPLEMENTAL_ARROWS_B = new Character$UnicodeBlock("SUPPLEMENTAL_ARROWS_B", new String[]{"Supplemental Arrows-B", "SupplementalArrows-B"});
    public static final Character$UnicodeBlock MISCELLANEOUS_MATHEMATICAL_SYMBOLS_B = new Character$UnicodeBlock("MISCELLANEOUS_MATHEMATICAL_SYMBOLS_B", new String[]{"Miscellaneous Mathematical Symbols-B", "MiscellaneousMathematicalSymbols-B"});
    public static final Character$UnicodeBlock SUPPLEMENTAL_MATHEMATICAL_OPERATORS = new Character$UnicodeBlock("SUPPLEMENTAL_MATHEMATICAL_OPERATORS", new String[]{"Supplemental Mathematical Operators", "SupplementalMathematicalOperators"});
    public static final Character$UnicodeBlock MISCELLANEOUS_SYMBOLS_AND_ARROWS = new Character$UnicodeBlock("MISCELLANEOUS_SYMBOLS_AND_ARROWS", new String[]{"Miscellaneous Symbols and Arrows", "MiscellaneousSymbolsandArrows"});
    public static final Character$UnicodeBlock KATAKANA_PHONETIC_EXTENSIONS = new Character$UnicodeBlock("KATAKANA_PHONETIC_EXTENSIONS", new String[]{"Katakana Phonetic Extensions", "KatakanaPhoneticExtensions"});
    public static final Character$UnicodeBlock YIJING_HEXAGRAM_SYMBOLS = new Character$UnicodeBlock("YIJING_HEXAGRAM_SYMBOLS", new String[]{"Yijing Hexagram Symbols", "YijingHexagramSymbols"});
    public static final Character$UnicodeBlock VARIATION_SELECTORS = new Character$UnicodeBlock("VARIATION_SELECTORS", new String[]{"Variation Selectors", "VariationSelectors"});
    public static final Character$UnicodeBlock LINEAR_B_SYLLABARY = new Character$UnicodeBlock("LINEAR_B_SYLLABARY", new String[]{"Linear B Syllabary", "LinearBSyllabary"});
    public static final Character$UnicodeBlock LINEAR_B_IDEOGRAMS = new Character$UnicodeBlock("LINEAR_B_IDEOGRAMS", new String[]{"Linear B Ideograms", "LinearBIdeograms"});
    public static final Character$UnicodeBlock AEGEAN_NUMBERS = new Character$UnicodeBlock("AEGEAN_NUMBERS", new String[]{"Aegean Numbers", "AegeanNumbers"});
    public static final Character$UnicodeBlock OLD_ITALIC = new Character$UnicodeBlock("OLD_ITALIC", new String[]{"Old Italic", "OldItalic"});
    public static final Character$UnicodeBlock GOTHIC = new Character$UnicodeBlock("GOTHIC");
    public static final Character$UnicodeBlock UGARITIC = new Character$UnicodeBlock("UGARITIC");
    public static final Character$UnicodeBlock DESERET = new Character$UnicodeBlock("DESERET");
    public static final Character$UnicodeBlock SHAVIAN = new Character$UnicodeBlock("SHAVIAN");
    public static final Character$UnicodeBlock OSMANYA = new Character$UnicodeBlock("OSMANYA");
    public static final Character$UnicodeBlock CYPRIOT_SYLLABARY = new Character$UnicodeBlock("CYPRIOT_SYLLABARY", new String[]{"Cypriot Syllabary", "CypriotSyllabary"});
    public static final Character$UnicodeBlock BYZANTINE_MUSICAL_SYMBOLS = new Character$UnicodeBlock("BYZANTINE_MUSICAL_SYMBOLS", new String[]{"Byzantine Musical Symbols", "ByzantineMusicalSymbols"});
    public static final Character$UnicodeBlock MUSICAL_SYMBOLS = new Character$UnicodeBlock("MUSICAL_SYMBOLS", new String[]{"Musical Symbols", "MusicalSymbols"});
    public static final Character$UnicodeBlock TAI_XUAN_JING_SYMBOLS = new Character$UnicodeBlock("TAI_XUAN_JING_SYMBOLS", new String[]{"Tai Xuan Jing Symbols", "TaiXuanJingSymbols"});
    public static final Character$UnicodeBlock MATHEMATICAL_ALPHANUMERIC_SYMBOLS = new Character$UnicodeBlock("MATHEMATICAL_ALPHANUMERIC_SYMBOLS", new String[]{"Mathematical Alphanumeric Symbols", "MathematicalAlphanumericSymbols"});
    public static final Character$UnicodeBlock CJK_UNIFIED_IDEOGRAPHS_EXTENSION_B = new Character$UnicodeBlock("CJK_UNIFIED_IDEOGRAPHS_EXTENSION_B", new String[]{"CJK Unified Ideographs Extension B", "CJKUnifiedIdeographsExtensionB"});
    public static final Character$UnicodeBlock CJK_COMPATIBILITY_IDEOGRAPHS_SUPPLEMENT = new Character$UnicodeBlock("CJK_COMPATIBILITY_IDEOGRAPHS_SUPPLEMENT", new String[]{"CJK Compatibility Ideographs Supplement", "CJKCompatibilityIdeographsSupplement"});
    public static final Character$UnicodeBlock TAGS = new Character$UnicodeBlock("TAGS");
    public static final Character$UnicodeBlock VARIATION_SELECTORS_SUPPLEMENT = new Character$UnicodeBlock("VARIATION_SELECTORS_SUPPLEMENT", new String[]{"Variation Selectors Supplement", "VariationSelectorsSupplement"});
    public static final Character$UnicodeBlock SUPPLEMENTARY_PRIVATE_USE_AREA_A = new Character$UnicodeBlock("SUPPLEMENTARY_PRIVATE_USE_AREA_A", new String[]{"Supplementary Private Use Area-A", "SupplementaryPrivateUseArea-A"});
    public static final Character$UnicodeBlock SUPPLEMENTARY_PRIVATE_USE_AREA_B = new Character$UnicodeBlock("SUPPLEMENTARY_PRIVATE_USE_AREA_B", new String[]{"Supplementary Private Use Area-B", "SupplementaryPrivateUseArea-B"});
    public static final Character$UnicodeBlock HIGH_SURROGATES = new Character$UnicodeBlock("HIGH_SURROGATES", new String[]{"High Surrogates", "HighSurrogates"});
    public static final Character$UnicodeBlock HIGH_PRIVATE_USE_SURROGATES = new Character$UnicodeBlock("HIGH_PRIVATE_USE_SURROGATES", new String[]{"High Private Use Surrogates", "HighPrivateUseSurrogates"});
    public static final Character$UnicodeBlock LOW_SURROGATES = new Character$UnicodeBlock("LOW_SURROGATES", new String[]{"Low Surrogates", "LowSurrogates"});
    private static final int[] blockStarts = {0, 128, 256, 384, 592, 688, 768, 880, 1024, 1280, 1328, 1424, 1536, 1792, 1872, 1920, 1984, 2304, 2432, 2560, 2688, 2816, 2944, 3072, 3200, 3328, 3456, 3584, 3712, 3840, 4096, 4256, 4352, 4608, 4992, 5024, 5120, 5760, 5792, 5888, 5920, 5952, 5984, 6016, 6144, 6320, 6400, 6480, 6528, 6624, 6656, 7424, 7552, 7680, 7936, 8192, 8304, 8352, 8400, 8448, 8528, 8592, 8704, 8960, 9216, 9280, 9312, 9472, 9600, 9632, 9728, 9984, 10176, 10224, 10240, 10496, 10624, 10752, 11008, 11264, 11904, 12032, 12256, 12272, 12288, 12352, 12448, 12544, 12592, 12688, 12704, 12736, 12784, 12800, 13056, 13312, 19904, 19968, 40960, 42128, 42192, 44032, 55216, 55296, 56192, 56320, 57344, 63744, 64256, 64336, 65024, 65040, 65056, 65072, 65104, 65136, 65280, 65520, 65536, 65664, 65792, 65856, 66304, 66352, 66384, 66432, 66464, 66560, 66640, 66688, 66736, 67584, 67648, 118784, 119040, 119296, 119552, 119648, 119808, 120832, 131072, 173792, 194560, 195104, 917504, 917632, 917760, 918000, 983040, 1048576};
    private static final Character$UnicodeBlock[] blocks = {BASIC_LATIN, LATIN_1_SUPPLEMENT, LATIN_EXTENDED_A, LATIN_EXTENDED_B, IPA_EXTENSIONS, SPACING_MODIFIER_LETTERS, COMBINING_DIACRITICAL_MARKS, GREEK, CYRILLIC, CYRILLIC_SUPPLEMENTARY, ARMENIAN, HEBREW, ARABIC, SYRIAC, null, THAANA, null, DEVANAGARI, BENGALI, GURMUKHI, GUJARATI, ORIYA, TAMIL, TELUGU, KANNADA, MALAYALAM, SINHALA, THAI, LAO, TIBETAN, MYANMAR, GEORGIAN, HANGUL_JAMO, ETHIOPIC, null, CHEROKEE, UNIFIED_CANADIAN_ABORIGINAL_SYLLABICS, OGHAM, RUNIC, TAGALOG, HANUNOO, BUHID, TAGBANWA, KHMER, MONGOLIAN, null, LIMBU, TAI_LE, null, KHMER_SYMBOLS, null, PHONETIC_EXTENSIONS, null, LATIN_EXTENDED_ADDITIONAL, GREEK_EXTENDED, GENERAL_PUNCTUATION, SUPERSCRIPTS_AND_SUBSCRIPTS, CURRENCY_SYMBOLS, COMBINING_MARKS_FOR_SYMBOLS, LETTERLIKE_SYMBOLS, NUMBER_FORMS, ARROWS, MATHEMATICAL_OPERATORS, MISCELLANEOUS_TECHNICAL, CONTROL_PICTURES, OPTICAL_CHARACTER_RECOGNITION, ENCLOSED_ALPHANUMERICS, BOX_DRAWING, BLOCK_ELEMENTS, GEOMETRIC_SHAPES, MISCELLANEOUS_SYMBOLS, DINGBATS, MISCELLANEOUS_MATHEMATICAL_SYMBOLS_A, SUPPLEMENTAL_ARROWS_A, BRAILLE_PATTERNS, SUPPLEMENTAL_ARROWS_B, MISCELLANEOUS_MATHEMATICAL_SYMBOLS_B, SUPPLEMENTAL_MATHEMATICAL_OPERATORS, MISCELLANEOUS_SYMBOLS_AND_ARROWS, null, CJK_RADICALS_SUPPLEMENT, KANGXI_RADICALS, null, IDEOGRAPHIC_DESCRIPTION_CHARACTERS, CJK_SYMBOLS_AND_PUNCTUATION, HIRAGANA, KATAKANA, BOPOMOFO, HANGUL_COMPATIBILITY_JAMO, KANBUN, BOPOMOFO_EXTENDED, null, KATAKANA_PHONETIC_EXTENSIONS, ENCLOSED_CJK_LETTERS_AND_MONTHS, CJK_COMPATIBILITY, CJK_UNIFIED_IDEOGRAPHS_EXTENSION_A, YIJING_HEXAGRAM_SYMBOLS, CJK_UNIFIED_IDEOGRAPHS, YI_SYLLABLES, YI_RADICALS, null, HANGUL_SYLLABLES, null, HIGH_SURROGATES, HIGH_PRIVATE_USE_SURROGATES, LOW_SURROGATES, PRIVATE_USE_AREA, CJK_COMPATIBILITY_IDEOGRAPHS, ALPHABETIC_PRESENTATION_FORMS, ARABIC_PRESENTATION_FORMS_A, VARIATION_SELECTORS, null, COMBINING_HALF_MARKS, CJK_COMPATIBILITY_FORMS, SMALL_FORM_VARIANTS, ARABIC_PRESENTATION_FORMS_B, HALFWIDTH_AND_FULLWIDTH_FORMS, SPECIALS, LINEAR_B_SYLLABARY, LINEAR_B_IDEOGRAMS, AEGEAN_NUMBERS, null, OLD_ITALIC, GOTHIC, null, UGARITIC, null, DESERET, SHAVIAN, OSMANYA, null, CYPRIOT_SYLLABARY, null, BYZANTINE_MUSICAL_SYMBOLS, MUSICAL_SYMBOLS, null, TAI_XUAN_JING_SYMBOLS, null, MATHEMATICAL_ALPHANUMERIC_SYMBOLS, null, CJK_UNIFIED_IDEOGRAPHS_EXTENSION_B, null, CJK_COMPATIBILITY_IDEOGRAPHS_SUPPLEMENT, null, TAGS, null, VARIATION_SELECTORS_SUPPLEMENT, null, SUPPLEMENTARY_PRIVATE_USE_AREA_A, SUPPLEMENTARY_PRIVATE_USE_AREA_B};
    
    public static Character$UnicodeBlock of(char c) {
        return of((int)c);
    }
    
    public static Character$UnicodeBlock of(int codePoint) {
        if (!Character.isValidCodePoint(codePoint)) {
            throw new IllegalArgumentException();
        }
        int top;
        int bottom;
        int current;
        bottom = 0;
        top = blockStarts.length;
        current = top / 2;
        while (top - bottom > 1) {
            if (codePoint >= blockStarts[current]) {
                bottom = current;
            } else {
                top = current;
            }
            current = (top + bottom) / 2;
        }
        return blocks[current];
    }
    
    public static final Character$UnicodeBlock forName(String blockName) {
        Character$UnicodeBlock block = (Character$UnicodeBlock)(Character$UnicodeBlock)map.get(blockName.toUpperCase(Locale.US));
        if (block == null) {
            throw new IllegalArgumentException();
        }
        return block;
    }
}
