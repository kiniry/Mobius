// Tests bad syntax of the signals_only clause

public class SignalsOnlyBad {

/*@
	signals_only;
	signals_only NullPointerException ,, Exception;
	signals_only , Exception;
	signals_only  String;
	signals_only Q;
*/
	public void m();
}
