package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.List;

import junit.framework.TestCase;


public class FileCheckerTest extends TestCase {
	
	public final static String space="[\\s+]";
	public final static String CLASS_REP="(\\w+.class)";
	public final static String DATE_REP="(\\d+)";
	public final static String DESCRIPTION_REP="(.+)";
	public final static String EMAIL_REP="(\\w+@\\w+\\.(:?com|ie))";
	public final static String EXPRESSION_REP="(.+)";
	public final static String FLOAT_REP="([1-9]+\\.[0-9]+)";
	public final static String INT_REP="((?:+|-)[1-9][0-9]+)";
	public final static String STRING_REP="(.+)";
	public final static String THROWABLE_REP="((?:\\w+).java)";
	public final static String URL_REP="((?:(?:http[s]?|ftp):\\/)?\\/?(?:[^:\\/\\s]+)(?:(?:\\/\\w+)*\\/)(?:[\\w\\-\\.]+[^#?\\s]+)(?:.*)?(?:#[\\w\\-]+)?)";
	public final static String VERSION_REP="([0-9](?:.[0-9])*)";

	
	public void testCorrectExampleOne(){
		
		String correctReg=
			"correctexample1"+space+
			"a"+space+
			"b"+space+
			"<c="+CLASS_REP+">"+space+
			"<d="+DATE_REP+">"+space+
			"<e="+DESCRIPTION_REP+">"+space+
			"<f="+EMAIL_REP+">"+space+
			"<g="+EXPRESSION_REP+">"+space+
			"<h="+FLOAT_REP+">"+space+
			"<i="+INT_REP+">"+space+"" +
			"<j="+STRING_REP+">"+space+
			"<k="+THROWABLE_REP+">"+space+
			"<l="+URL_REP+">"+space+
			"<m="+VERSION_REP+">";
		
		LinkedHashMap<String, Integer> correctMap=new LinkedHashMap<String, Integer>();
		correctMap.put("c",1);
		correctMap.put("d",2);
		correctMap.put("e",3);
		correctMap.put("f",4);
		correctMap.put("g",5);
		correctMap.put("h",6);
		correctMap.put("i",7);
		correctMap.put("j",8);
		correctMap.put("k",9);
		correctMap.put("l",10);
		correctMap.put("m",11);
		
		
		
		File caseOne= new File("resources/examples/correctexample1.yaml");
		FileChecker checkOne= new FileChecker(caseOne);
		checkOne.processProps();
		List<Property> listOProp=checkOne.getProps();
		String checkReg="";
		LinkedHashMap<String,Integer> checkMap= new LinkedHashMap<String,Integer>();
		for(Property current: listOProp){
			checkReg+=(current.getReg()).getExp();
			checkMap=(current.getReg()).getGroups();
			
		}
		
//		System.out.println(correctReg);
//		System.out.println(checkReg);
//		assertEquals(correctReg,checkReg);
//		assertEquals(correctMap,checkMap);
	}
	public void testCorrectExampleTwo(){
		
		
		String correctReg=
			"correctexample2"+space+
			"a"+space+
			"b"+space+
			"(?:<c="+CLASS_REP+">|"+
				"<d="+DATE_REP+">|"+
				"<e="+DESCRIPTION_REP+">"+
			")"+space+
			"<f="+EMAIL_REP+">"+space+
			"<g="+EXPRESSION_REP+">"+space+
			"(?:<h="+FLOAT_REP+">()()|"+
				"<i="+INT_REP+">"+space+
				"(i1()|"+
					"i2()|"+
					"<i3="+INT_REP+">"+
				")"+
			")"+space+	
			"<j="+STRING_REP+">"+space+
			"<k="+THROWABLE_REP+">"+space+
			"(?:<l="+URL_REP+">|"+
				"<m="+VERSION_REP+">"+
			")";
		
		LinkedHashMap<String, Integer> correctMap=new LinkedHashMap<String, Integer>();
		correctMap.put("c",1);
		correctMap.put("d",1);
		correctMap.put("e",1);
		correctMap.put("f",2);
		correctMap.put("g",3);
		correctMap.put("h",4);
		correctMap.put("i",4);
		correctMap.put("is",5);
		correctMap.put("i3",6);
		correctMap.put("j",7);
		correctMap.put("k",8);
		correctMap.put("l",9);
		correctMap.put("m",9);
		
		
		
		File caseTwo= new File("resources/examples/correctexample2.yaml");
		FileChecker checkOne= new FileChecker(caseTwo);
		checkOne.processProps();
		List<Property> listOProp=checkOne.getProps();
		String checkReg="";
		LinkedHashMap<String,Integer> checkMap= new LinkedHashMap<String,Integer>();
		for(Property current: listOProp){
			checkReg+=(current.getReg()).getExp();
			checkMap=(current.getReg()).getGroups();
			
		}
//		System.out.println(correctMap);
//		System.out.println(checkMap);
//		System.out.println(correctReg);
//		System.out.println(checkReg);
		assertEquals(correctReg,checkReg);
		assertEquals(correctMap,checkMap);
	}
//	

}
