package bico;

import java.io.IOException;
import java.io.Writer;


/**
 * The dictonary creates a dictonary that can then be used to translate the
 * generated name into human-readable names.
 * 
 * @author Laurent.Hubert@irisa.fr
 */
interface Dictionary {

	/**
	 * Associate package implementation name coqPackageName to the corresponding
	 * java name. It also works if the association has already been done with
	 * the same name or with an other one.
	 * 
	 * @param javaName
	 * @param coqPackageName
	 */
	public void addPackage(String javaName, int coqPackageName);

	/**
	 * @param javaName
	 * @return the implementation name corresponding to javaName or 0 if unfound
	 */
	public int getCoqPackageName(String javaName);

	/**
	 * Associate a class implementation name to the corresponding java name. It
	 * also works if the association has already been done with the same name or
	 * with an other one.
	 * 
	 * @param javaName
	 *            the corresponding human readable name
	 * @param coqPackageName
	 *            the Biclano package name
	 * @param coqClassName
	 *            the Bicolano class name
	 */
	public void addClass(String javaName, int coqPackageName, int coqClassName);

	/**
	 * Associate a field implementation name to the corresponding java name. It
	 * also works if the association has already been done with the same name or
	 * with an other one.
	 * 
	 * @param javaName
	 *            the corresponding human readable name
	 * @param coqPackageName
	 *            the Biclano package name
	 * @param coqClassName
	 *            the Biclano class name
	 * @param coqFieldName
	 *            the Biclano field name
	 */
	public void addField(String javaName, int coqPackageName, int coqClassName,
			int coqFieldName);

	/**
	 * Associate a method implementation name to the corresponding java name. It
	 * also works if the association has already been done with the same name or
	 * with an other one.
	 * 
	 * @param javaName
	 *            the corresponding human readable name
	 * @param coqPackageName
	 *            the Bicolano package name
	 * @param coqClassName
	 *            the Bicolano class name
	 * @param coqMethodName
	 *            the Bicolano method name
	 */
	public void addMethod(String javaName, int coqPackageName,
			int coqClassName, int coqMethodName);
	
	public void write(Writer out) throws IOException;
}