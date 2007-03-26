package mobius.directVCGen.formula.type;

public class NumType extends Type {
	/** a constructor */
	NumType(String desc) {
		super(desc);
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object o) {
		return (o instanceof NumType);
	}
}
