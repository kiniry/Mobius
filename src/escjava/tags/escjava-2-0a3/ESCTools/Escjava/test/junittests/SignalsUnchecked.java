public class SignalsUnchecked
{
    // Redundant specification of unchecked exceptions.
    //@ requires true;
    //@ ensures true;
    //@ signals (java.lang.RuntimeException) true;
    //@ signals (java.lang.Error) true;
    public void redundant_signals_unchecked() {
        ;
    }
}
