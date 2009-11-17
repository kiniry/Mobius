package java.util;

import java.security.PrivilegedAction;

class Currency$1 implements PrivilegedAction {
    
    Currency$1() {
        
    }
    
    public Object run() {
        try {
            Class data = Class.forName("java.util.CurrencyData");
            Currency.mainTable = (String)(String)data.getDeclaredField("mainTable").get(data);
            Currency.scCutOverTimes = (long[])(long[])data.getDeclaredField("scCutOverTimes").get(data);
            Currency.scOldCurrencies = (String[])(String[])data.getDeclaredField("scOldCurrencies").get(data);
            Currency.scNewCurrencies = (String[])(String[])data.getDeclaredField("scNewCurrencies").get(data);
            Currency.scOldCurrenciesDFD = (int[])(int[])data.getDeclaredField("scOldCurrenciesDFD").get(data);
            Currency.scNewCurrenciesDFD = (int[])(int[])data.getDeclaredField("scNewCurrenciesDFD").get(data);
            Currency.otherCurrencies = (String)(String)data.getDeclaredField("otherCurrencies").get(data);
            Currency.otherCurrenciesDFD = (int[])(int[])data.getDeclaredField("otherCurrenciesDFD").get(data);
        } catch (ClassNotFoundException e) {
            throw new InternalError();
        } catch (NoSuchFieldException e) {
            throw new InternalError();
        } catch (IllegalAccessException e) {
            throw new InternalError();
        }
        return null;
    }
}
