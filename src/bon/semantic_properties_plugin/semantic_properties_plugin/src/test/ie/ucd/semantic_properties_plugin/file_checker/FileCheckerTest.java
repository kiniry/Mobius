package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import semantic_properties_plugin.custom_objects.MyObjectKind;

import junit.framework.TestCase;


public class FileCheckerTest extends TestCase {
	
	public final static String space="[\\s+]";
	public final static String CLASS_REP=MyObjectKind.Class.getReg();
	public final static String DATE_REP=MyObjectKind.Date.getReg();
	public final static String DESCRIPTION_REP=MyObjectKind.Description.getReg();
	public final static String EMAIL_REP=MyObjectKind.Email.getReg();
	public final static String EXPRESSION_REP=MyObjectKind.Expression.getReg();
	public final static String FLOAT_REP=MyObjectKind.MyFloat.getReg();
	public final static String INT_REP=MyObjectKind.MyInt.getReg();
	public final static String STRING_REP=MyObjectKind.String.getReg();
	public final static String THROWABLE_REP=MyObjectKind.Throwable.getReg();
	public final static String URL_REP=MyObjectKind.URL.getReg();
	public final static String VERSION_REP=MyObjectKind.Version.getReg();

//	
//	public void testCorrectExampleOne(){
//		
//		String correctReg=
//			"correctexample1"+space+
//			"a"+space+
//			"b"+space+
//			CLASS_REP+space+
//			DATE_REP+space+
//			DESCRIPTION_REP+space+
//			EMAIL_REP+space+
//			EXPRESSION_REP+space+
//			FLOAT_REP+space+
//			INT_REP+space+"" +
//			STRING_REP+space+
//			THROWABLE_REP+space+
//			URL_REP+space+
//			VERSION_REP;
//		
//		LinkedHashMap<String, Integer> correctMap=new LinkedHashMap<String, Integer>();
//		correctMap.put("c",1);
//		correctMap.put("d",2);
//		correctMap.put("e",3);
//		correctMap.put("f",4);
//		correctMap.put("g",5);
//		correctMap.put("h",6);
//		correctMap.put("i",7);
//		correctMap.put("j",8);
//		correctMap.put("k",9);
//		correctMap.put("l",10);
//		correctMap.put("m",11);
//		
//		
//		
//		File caseOne= new File("resources/examples/correctexample1.yaml");
//		SemanticProperty checkOne= new SemanticProperty(caseOne);
//
//		List<LevelRepresenation> listOProp=checkOne.getProps();
//		String checkReg="";
//		LinkedHashMap<String,Integer> checkMap= new LinkedHashMap<String,Integer>();
//		for(LevelRepresenation current: listOProp){
//			checkReg+=(current.getReg()).getExp();
//			checkMap=(current.getReg()).getGroupInt();
//			
//		}
//		
////		System.out.println(correctReg);
////		System.out.println(correctMap);
////		System.out.println(checkReg);
//		assertEquals(correctReg,checkReg);
//		assertEquals(correctMap,checkMap);
//	}
//	public void testCorrectExampleTwo(){
//		
//		
//		String correctReg=
//			"correctexample2"+space+
//			"a"+space+
//			"b"+space+
//			"(?:"+CLASS_REP+"|"+
//				DATE_REP+"|"+
//				DESCRIPTION_REP+
//			")"+space+
//			EMAIL_REP+space+
//			EXPRESSION_REP+space+
//			"(?:"+FLOAT_REP+"|"+
//				INT_REP+space+
//				"(i1|"+
//					"i2|"+
//					INT_REP+
//				")"+
//			")"+space+	
//			STRING_REP+space+
//			THROWABLE_REP+space+
//			"(?:"+URL_REP+"|"+
//				VERSION_REP+
//			")";
//		
//		LinkedHashMap<String, Integer> correctMap=new LinkedHashMap<String, Integer>();
//		correctMap.put("c",1);
//		correctMap.put("d",2);
//		correctMap.put("e",3);
//		correctMap.put("f",4);
//		correctMap.put("g",5);
//		correctMap.put("h",6);
//		correctMap.put("i",7);
//		correctMap.put("is",8);
//		correctMap.put("i3",9);
//		correctMap.put("j",10);
//		correctMap.put("k",11);
//		correctMap.put("l",12);
//		correctMap.put("m", 13);
//		
//		
//		
//		File caseTwo= new File("resources/examples/correctexample2.yaml");
//		SemanticProperty checkOne= new SemanticProperty(caseTwo);
//		
//		List<LevelRepresenation> listOProp=checkOne.getProps();
//		String checkReg="";
//		LinkedHashMap<String,Integer> checkMap= new LinkedHashMap<String,Integer>();
//		for(LevelRepresenation current: listOProp){
//			checkReg+=(current.getReg()).getExp();
//			checkMap=(current.getReg()).getGroupInt();
//			
//		}
////		System.out.println(correctMap);
////		System.out.println(checkMap);
////		System.out.println(correctReg);
////		System.out.println(checkReg);
//		assertEquals(correctReg,checkReg);
//		assertEquals(correctMap,checkMap);
//	}
//	
//	public void testConcurrencyExample() {
//		/**
//		 * string to check
//		 */
//		String propInstance=
//			"concurrency TIMEOUT 20 java.lang.Throwable a short  description.";
//
//		
//		File caseThree = new File("resources/examples/concurrency.yaml");
//		SemanticProperty checkThree = new SemanticProperty(caseThree);
//		//checkThree.printProps();
//		assertTrue(checkThree.check(propInstance));
//		
//		String propInstance2=
//			"concurrency CONCURRENT ";
//
//		assertTrue(checkThree.check(propInstance2));
//		//maps dont equal
//		//assertEquals(correctMap,checkMap);
//	}

}
