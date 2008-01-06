package jml2bml.bytecode;

/**
 * Class representing BML annotation ready to insert into the bytecode.
 * 
 * @author Jedrek
 * 
 */
public class BmlAnnotation {
	private Location location;
	private String annotation;

	/**
	 * Creates a new instance of the BML Annotation.
	 * 
	 * @param annotation -
	 *            text of the inserted annotation
	 * @param location -
	 *            location in the bytecode, where the annotation should be
	 *            inserted
	 */
	public BmlAnnotation(String annotation, Location location) {
		this.annotation = annotation;
		this.location = location;
	}

	public Location getLocation() {
		return location;
	}

	public String getAnnotation() {
		return annotation;
	}
}
