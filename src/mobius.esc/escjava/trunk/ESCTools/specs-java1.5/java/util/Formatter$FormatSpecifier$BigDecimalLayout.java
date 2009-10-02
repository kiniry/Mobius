package java.util;

import java.math.BigInteger;

class Formatter$FormatSpecifier$BigDecimalLayout {
    /*synthetic*/ final Formatter$FormatSpecifier this$1;
    private StringBuilder mant;
    private StringBuilder exp;
    private boolean dot = false;
    
    public Formatter$FormatSpecifier$BigDecimalLayout(/*synthetic*/ final Formatter$FormatSpecifier this$1, BigInteger intVal, int scale, Formatter$BigDecimalLayoutForm form) {
        this.this$1 = this$1;
        
        layout(intVal, scale, form);
    }
    
    public boolean hasDot() {
        return dot;
    }
    
    public char[] layoutChars() {
        StringBuilder sb = new StringBuilder(mant);
        if (exp != null) {
            sb.append('E');
            sb.append(exp);
        }
        return toCharArray(sb);
    }
    
    public char[] mantissa() {
        return toCharArray(mant);
    }
    
    public char[] exponent() {
        return toCharArray(exp);
    }
    
    private char[] toCharArray(StringBuilder sb) {
        if (sb == null) return null;
        char[] result = new char[sb.length()];
        sb.getChars(0, result.length, result, 0);
        return result;
    }
    
    private void layout(BigInteger intVal, int scale, Formatter$BigDecimalLayoutForm form) {
        char[] coeff = intVal.toString().toCharArray();
        mant = new StringBuilder(coeff.length + 14);
        if (scale == 0) {
            int len = coeff.length;
            if (len > 1) {
                mant.append(coeff[0]);
                if (form == Formatter$BigDecimalLayoutForm.SCIENTIFIC) {
                    mant.append('.');
                    dot = true;
                    mant.append(coeff, 1, len - 1);
                    exp = new StringBuilder("+");
                    if (len < 10) exp.append("0").append(len - 1); else exp.append(len - 1);
                } else {
                    mant.append(coeff, 1, len - 1);
                }
            } else {
                mant.append(coeff);
                if (form == Formatter$BigDecimalLayoutForm.SCIENTIFIC) exp = new StringBuilder("+00");
            }
            return;
        }
        long adjusted = -(long)scale + (coeff.length - 1);
        if (form == Formatter$BigDecimalLayoutForm.DECIMAL_FLOAT) {
            int pad = scale - coeff.length;
            if (pad >= 0) {
                mant.append("0.");
                dot = true;
                for (; pad > 0; pad--) mant.append('0');
                mant.append(coeff);
            } else {
                mant.append(coeff, 0, -pad);
                mant.append('.');
                dot = true;
                mant.append(coeff, -pad, scale);
            }
        } else {
            mant.append(coeff[0]);
            if (coeff.length > 1) {
                mant.append('.');
                dot = true;
                mant.append(coeff, 1, coeff.length - 1);
            }
            exp = new StringBuilder();
            if (adjusted != 0) {
                long abs = Math.abs(adjusted);
                exp.append(adjusted < 0 ? '-' : '+');
                if (abs < 10) exp.append('0');
                exp.append(abs);
            } else {
                exp.append("+00");
            }
        }
    }
}
