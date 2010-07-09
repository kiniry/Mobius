/**
 * test the regexs for all the custom objects
 */
package ie.ucd.semantic_properties_plugin.custom_objects;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import semantic_properties_plugin.custom_objects.MyClass;
import semantic_properties_plugin.custom_objects.MyDate;
import semantic_properties_plugin.custom_objects.MyDescription;
import semantic_properties_plugin.custom_objects.MyEmail;
import semantic_properties_plugin.custom_objects.MyExpression;
import semantic_properties_plugin.custom_objects.MyFloat;
import semantic_properties_plugin.custom_objects.MyInt;
import semantic_properties_plugin.custom_objects.MyString;
import semantic_properties_plugin.custom_objects.MyThrowable;
import semantic_properties_plugin.custom_objects.MyURL;
import semantic_properties_plugin.custom_objects.MyVersion;
import semantic_properties_plugin.custom_objects.Nat;
import junit.framework.TestCase;

public class MyObjectTest extends TestCase {

	public void testMyClass() {
		MyClass objectToTest = new MyClass();
		Pattern p = Pattern.compile(objectToTest.getReg());

		/**
		 * TRUE CASES
		 */

		String posOne = "java.lang.Throwable";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "java.bls3ah.Bla0h";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "java.ih.inn$er.Another";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "jav";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "jav.hi.1per§";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

	}

	/* Check MyTest Object.
	 */
	public void testMyDate() {
		MyDate objectToTest = new MyDate();
		Pattern p = Pattern.compile(objectToTest.getReg());

		/**
		 * TRUE CASES
		 */
		String correctValueOne = "24/10/2004";
		Matcher m = p.matcher(correctValueOne);
		assertTrue(m.matches());

		/**
		 * Works but could be improved but is difficult to account for leap year
		 * Other possibility:
		 * ^[0,1]?\\d{1}\\/(?:(?:[0-2]?\\d{1})|(?:[3][0,1]{1})
		 * )\\/(?:\\d)|([2-9]{1}\d{3}))$
		 */
		String correctValueTwo = "89/90/2004";
		Matcher mTwo = p.matcher(correctValueTwo);
		assertTrue(mTwo.matches());

		String correctValueThree = "01-10-2004";
		Matcher mThree = p.matcher(correctValueThree);
		assertTrue(mThree.matches());

		/**
		 * FALSE CASES
		 */

		/**
		 * year has to be in form XXXX where x is a digit[0-9]
		 */
		String correctValueFour = "01-10-04";
		Matcher mFour = p.matcher(correctValueFour);
		assertFalse(mFour.matches());

	}

	public void testMyDescription() {
		MyDescription objectToTest = new MyDescription();
		Pattern p = Pattern.compile(objectToTest.getReg());

		/**
		 * TRUE CASES
		 */
		String correctValueOne = "this is a description.";
		Matcher m = p.matcher(correctValueOne);
		assertTrue(m.matches());

		String correctValueTwo = "Another V!@£$@! good  expression.";
		Matcher mTwo = p.matcher(correctValueTwo);
		assertTrue(mTwo.matches());

		/**
		 * FALSE CASES
		 */

		String ValueThree = "not valid . . . ";
		Matcher mThree = p.matcher(ValueThree);
		assertFalse(mThree.matches());

		String ValueFour = "not valid";
		Matcher mFour = p.matcher(ValueFour);
		assertFalse(mFour.matches());

		String ValueFive = "not valid. ";
		Matcher mFive = p.matcher(ValueFive);
		assertFalse(mFive.matches());

	}

	/**
	 * make MyEmail object and create pattern from the regex then test against
	 * various forms of email
	 */
	public void testMyEmail() {

		MyEmail emailObject = new MyEmail();
		String emailObjectRegEx = emailObject.getReg();
		Pattern p = Pattern.compile(emailObjectRegEx);

		/**
		 * TRUE CASES
		 */
		String posEmailOne = "eoin@anadress.com";
		Matcher mOne = p.matcher(posEmailOne);
		assertTrue(mOne.matches());

		String posEmailTwo = "eoin.o-connor@domain-subdomain.de";
		Matcher mTwo = p.matcher(posEmailTwo);
		assertTrue(mTwo.matches());

		/**
		 * FALSE CASES
		 */
		String posEmailThree = "notanEmail";
		Matcher mThree = p.matcher(posEmailThree);
		assertFalse(mThree.matches());

		String posEmailFour = "email@hello.commmm";
		Matcher mFour = p.matcher(posEmailFour);
		assertFalse(mFour.matches());

		String posEmailFive = "no_underscores_allowed@hello.commmm";
		Matcher mFive = p.matcher(posEmailFive);
		assertFalse(mFive.matches());
	}

	public void testMyExpression() {

		MyExpression testObject = new MyExpression();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "(eoin@anadress.com)";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "(X==y+^)";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		/**
		 * maybe shouldn't work
		 */
		String posFive = "(((an expression)))";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = " (expression)";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "x=f";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

	}

	public void testMyFloat() {

		MyFloat testObject = new MyFloat();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "1001.202010";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "-1.0";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "+0.001";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = ".1";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "1.0.0";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

	}

	public void testMyInt() {

		MyInt testObject = new MyInt();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "123123";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "-1221312";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "+1231";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "212.23";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "-+1";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

	}

	/**
	 * MyString is a single word with any non white space characters a
	 * traditional java string "example string" is not valid. That would
	 *  be a MyDescription
	 */
	public void testMyString() {
		MyString objectToTest = new MyString();
		Pattern p = Pattern.compile(objectToTest.getReg());

		/**
		 * TRUE CASES
		 */
		String correctValueOne = "''";
		Matcher m = p.matcher(correctValueOne);
		assertTrue(m.matches());

		String correctValueTwo = "'thi$_1$_&_ A _$tri„g'";
		Matcher mTwo = p.matcher(correctValueTwo);
		assertTrue(mTwo.matches());

		/**
		 * FALSE CASES
		 */
		String correctValueThree = " notastring ";
		Matcher mThree = p.matcher(correctValueThree);
		assertFalse(mThree.matches());

		String correctValueFour = "definately not a string";
		Matcher mFour = p.matcher(correctValueFour);
		assertFalse(mFour.matches());
		

		String correctValueFive = " ";
		Matcher mFive = p.matcher(correctValueFive);
		assertFalse(mFive.matches());

	}

	public void testMyThrowable() {

		MyThrowable testObject = new MyThrowable();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "java.lang.Throwable";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "java.bls3ah.Bla0h";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "java.ih.inn$er.Another";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "jav";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "jav.hi.1per§";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

	}

	public void testMyURL() {

		MyURL testObject = new MyURL();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "ftp://www.anything.st.all";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "https://same.as.above";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "mailto:eoin@mail.com";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "www.hi.com";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "noturl";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());
	}

	public void testMyVersion() {

		MyVersion testObject = new MyVersion();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "1";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "1.2";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "1.3.4";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "1.4a";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "3.4b";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());
	}

	public void testMyNat() {

		Nat testObject = new Nat();
		String ObjectRegEx = testObject.getReg();
		Pattern p = Pattern.compile(ObjectRegEx);

		/**
		 * TRUE CASES
		 */

		String posOne = "1412341";
		Matcher mOne = p.matcher(posOne);
		assertTrue(mOne.matches());

		String posTwo = "1000.00";
		Matcher mTwo = p.matcher(posTwo);
		assertTrue(mTwo.matches());

		String posFive = "00056";
		Matcher mFive = p.matcher(posFive);
		assertTrue(mFive.matches());

		/**
		 * FALSE CASES
		 */
		String posThree = "-1";
		Matcher mThree = p.matcher(posThree);
		assertFalse(mThree.matches());

		String posFour = "3.4";
		Matcher mFour = p.matcher(posFour);
		assertFalse(mFour.matches());

		// 0 is not valid natural number can change
		String posSix = "0";
		Matcher mSix = p.matcher(posSix);
		assertFalse(mSix.matches());
	}

}
