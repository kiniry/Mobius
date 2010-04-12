import java.io.IOException;

import ie.ucd.gf.GF;
import ie.ucd.gf.GFProcess;
import ie.ucd.gf.api.GfCommands;
import ie.ucd.gf.impl.GfCommandsImpl;
import junit.framework.TestCase;


public class TestGFProcess extends TestCase {
	
	

	
	public void testGFProcessAlive()throws IOException{
		GfCommands command = new GfCommandsImpl();
		assertEquals(true, command.ProcessIsAlive());
		command.quitProcess();
		}

	
	public void testGFImports()throws IOException{
		GfCommands command = new GfCommandsImpl();	
		String output = command.importLanguage("CitizenlibEng");
		assertEquals("Languages: CitizenlibEng", output);
		output = command.importLanguage("CitizenlibBON");
		System.out.println(output);
		assertEquals("Languages: CitizenlibEng CitizenlibBON", output);
		command.quitProcess();
	}
		
	public void testGFTranslate()throws IOException{
		
		GfCommands command = new GfCommandsImpl();
		String output = command.importLanguage("CitizenlibEng");
		output = command.importLanguage("CitizenlibBON");
		output = command.translateSentence("CitizenlibEng","CitizenlibBON","what is its name");
		System.out.println(output);
		assertEquals("name : VALUE", output);
		output = command.translateSentence("CitizenlibEng","CitizenlibBON","is it single");
		System.out.println(output);
		assertEquals("single : BOOLEAN", output);
		command.quitProcess();
	}
	


}
