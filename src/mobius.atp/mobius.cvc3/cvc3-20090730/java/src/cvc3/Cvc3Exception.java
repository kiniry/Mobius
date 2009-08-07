package cvc3;

import java.util.*;

/** mirrors CVC3::Exception */
public class Cvc3Exception extends Exception {

    private final static long serialVersionUID = 1L;

    public Cvc3Exception(String message) {
	super(message);
    }
}
