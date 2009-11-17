package java.util;

class CurrencyData {
    
    CurrencyData() {
        
    }
    static final String mainTable = "\201CM\202\202KCF@\200R\203\201CF\201\204LCS\201\205Mc\005\205CCAKCM\206O\021CC\207E\210\210E\205\211\017\210XOBCOD\207\212J\201\005J\202OC\203JO\213M\201A\201CO\203\214\201\210O\202K\201\215O\214C\005\201\210\201\216P\203\205CC\207KJFEQ\201RQ\203cQ\n\201Cc\030RRQ\207\005\202V\026cCSJO\202\217QCKK\201KcC\201K@\203C\205JSO\203\201N\202\220QQJMQ\221C\222\205\207MN\201JQ\207\211CqAM\222JOQM\201\211\203\223\201\203\006Q\201\224A\005QCQFJCO\201\206JK\201\205RCCBOK\203\210\201\205AR\211\203LcO\225C\207CRGW\203CTR\201\202\226\203\203C\025\222SQ\201QJC";
    static final long[] scCutOverTimes = {9223372036854775807L, 9223372036854775807L, 9223372036854775807L, 1136059200000L, 9223372036854775807L, 9223372036854775807L, 9223372036854775807L, 9223372036854775807L, 9223372036854775807L, 1199138400000L, 9223372036854775807L, 9223372036854775807L, 1183248000000L, 9223372036854775807L, 9223372036854775807L, 1199142000000L, 1151704800000L, 9223372036854775807L, 9223372036854775807L, 1120165200000L, 1104530400000L, 1199160000000L};
    static final String[] scOldCurrencies = {"EUR", "XCD", "USD", "AZM", "XOF", "NOK", "AUD", "XAF", "NZD", "CYP", "MAD", "DKK", "GHC", "GBP", "CHF", "MTL", "MZM", "XPF", "ILS", "ROL", "TRL", "VEB"};
    static final String[] scNewCurrencies = {null, null, null, "AZN", null, null, null, null, null, "EUR", null, null, "GHS", null, null, "EUR", "MZN", null, null, "RON", "TRY", "VEF"};
    static final int[] scOldCurrenciesDFD = {2, 2, 2, 2, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 0, 2};
    static final int[] scNewCurrenciesDFD = {0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 2, 2, 2};
    static final String otherCurrencies = "ADP-AFA-ATS-AYM-AZM-AZN-BEF-BGL-BOV-BYB-CLF-CYP-DEM-ESP-EUR-FIM-FRF-GHC-GHP-GHS-GRD-GWP-IEP-ITL-LUF-MGF-MTL-MXV-MZM-MZN-NLG-PTE-ROL-RON-RUR-SDD-SIT-SRG-TPE-TRL-TRY-USN-USS-VEB-VEF-XAF-XAG-XAU-XBA-XBB-XBC-XBD-XCD-XDR-XFO-XFU-XOF-XPD-XPF-XPT-XTS-XXX-YUM";
    static final int[] otherCurrenciesDFD = {0, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 0, 2, 2, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2, 2, 0, 0, 2, 2, 2, 2, 2, 0, -1, -1, -1, -1, -1, -1, 2, -1, -1, -1, 0, -1, 0, -1, -1, -1, 2};
}
