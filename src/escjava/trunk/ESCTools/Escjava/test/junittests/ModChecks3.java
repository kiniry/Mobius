// This checks some unsupported uses of wildcards and ranges.

public class ModChecks3{

        //@ modifies aa[*][*];   // ERROR
        //@ modifies aa[*][0];   // ERROR
        //@ modifies aa[2..4][0];   // ERROR
        //@ modifies this.*.*;   // ERROR
	void zz() {}
}

