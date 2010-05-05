package ie.ucd.gf.test;

import java.io.IOException;
import java.util.Map;

import ie.ucd.gf.FileUtil;
import ie.ucd.gf.GF;
import ie.ucd.gf.GFProcess;
import ie.ucd.gf.api.GfCommands;
import ie.ucd.gf.impl.GfCommandsImpl;
import junit.framework.Assert;
import junit.framework.TestCase;


public class TestGFProcess extends TestCase {
	
	public void testCopySourceFiles()throws IOException{
		boolean copied = FileUtil.copyGFSourceFiles();
		assertEquals(true, copied);
		}

	

	public void testGFTranslateBON()throws IOException{
		
		GfCommands command = new GfCommandsImpl();
		String output = command.importLanguage("InformalBON");
		assertEquals("Languages: InformalBON", output);
		output = command.importLanguage("FormalBON");
		assertEquals("Languages: InformalBON FormalBON", output);
		output = command.translateSentenceToFormalBON("What is its name?");
		String output2 = command.translateSentenceToFormalBON("Is it single ?");
		System.out.println("BON TRANSLATION " + output2);
		command.quitProcess();
		System.out.println(output);
		assertEquals("name : VALUE", output);
		assertEquals("single : BOOLEAN", output2);
		
	}
	
public void testGFTranslateQuery()throws IOException{
		
		GfCommands command = new GfCommandsImpl();
		String output = command.importLanguage("InformalBON");
		assertEquals("Languages: InformalBON", output);
		output = command.importLanguage("FormalBON");
		assertEquals("Languages: InformalBON FormalBON", output);
		Map m = command.translateQueryToFormalBON("What is its name?");
		command.quitProcess();
		assertEquals("{name = VALUE}", m.toString());
		
		
	}
	
	
	public void testTranslateBONandStatement()throws IOException{
		
		GfCommands command = new GfCommandsImpl();
		String output = command.importLanguage("InformalBON");
		assertEquals("Languages: InformalBON", output);
		output = command.importLanguage("FormalBON");
		assertEquals("Languages: InformalBON FormalBON", output);
		output = command.translateSentenceToFormalBON("The car has 4 wheels and the car is moving.");
		command.quitProcess();
		System.out.println(output);
		assertEquals("wheel .count = 4 and car . moving", output);
	}

	
	public void testTranslateBONMultipleAnswers()throws IOException{
		
		GfCommands command = new GfCommandsImpl();
		String output = command.importLanguage("InformalBON");
		assertEquals("Languages: InformalBON", output);
		output = command.importLanguage("FormalBON");
		assertEquals("Languages: InformalBON FormalBON", output);
		output = command.translateSentenceFromFormalBON("house .count <= 2 and car .count > 2");
		command.quitProcess();
		System.out.println(output);
		assertEquals("It has at most 2 houses and there are than 2 cars.", output);
		
	}
	


}
