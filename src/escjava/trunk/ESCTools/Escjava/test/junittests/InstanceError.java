// Tests parsing of instance

class InstanceSuperC {

	//@ instance ghost public int ff; // OK
	//@ static instance ghost public int fff; // ERROR
	//@ static ghost instance public int ffff; // ERROR
	//@ ghost static instance public int fffff; // ERROR
	//@ instance model public int mm; // OK
	//@ static instance model public int mmm; // ERROR
}

interface InstanceSuper {

	//@ instance ghost public int ff; // OK
	//@ static instance ghost public int fff; // ERROR
	//@ static ghost instance public int ffff; // ERROR
	//@ ghost static instance public int fffff; // ERROR
	//@ instance model public int mm; // OK
	//@ static instance model public int mmm; // ERROR
}

public class InstanceError  implements InstanceSuper {
	//@ public instance static ghost boolean b1; // ERROR
	//@ public static instance ghost boolean b2; // ERROR
	//@ public instance ghost static boolean b3; // ERROR
	//@ public static ghost instance boolean b4; // ERROR
	//@ public ghost instance static boolean b5; // ERROR
	//@ public ghost static instance boolean b6; // ERROR
	//@ instance public ghost float f;	// OK
	//@ instance public model double d;	// OK
}

