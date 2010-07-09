package ie.ucd.semantic_properties_plugin.file_checker;

import java.io.File;

import junit.framework.TestCase;

public class ConcurrencyTest extends TestCase{

	
	public void  testConProp(){
		File conPropFile= new File("");
		
		Property concurrencyProperty=new Property(conPropFile);
		
		String sampleInput="";
		
		PropertyMatch match = new PropertyMatch(sampleInput,concurrencyProperty);
		
		assertTrue(match.isValid());
		
		
		File refPropFile=new File("");
		
		RefinementProperty refProp= new RefinementProperty(refPropFile);
		
		
		PropertyMatch refinedMatch=refProp.refine(match);
		
		assertTrue(refProp.isValidRefinement(refinedMatch,match));
		
		
		
		
	}
}
