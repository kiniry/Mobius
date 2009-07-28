// Tests the parsing of \nowarn etc. ops

public class WarnOpA {

	//@ ghost public \bigint i;

	// ERRORS:
	//@ ensures \warn() == 0;
	//@ ensures \nowarn(i,i+1) == -1;
	void n();
}
