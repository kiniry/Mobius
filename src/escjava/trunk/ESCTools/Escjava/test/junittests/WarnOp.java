// Tests the parsing of \nowarn etc. ops

public class WarnOp {

	//@ ghost public \bigint i = -1;

	//@ invariant \warn(i+1) == 0;
	//@ invariant \warn_op(i+1) == 0;
	//@ invariant \nowarn(i+1) == 0;
	//@ invariant \nowarn_op(i+1) == 0;
	//@ requires i == -1;
	void m() {}

}
