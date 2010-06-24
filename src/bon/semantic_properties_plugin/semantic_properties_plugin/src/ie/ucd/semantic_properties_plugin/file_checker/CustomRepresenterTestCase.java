package ie.ucd.semantic_properties_plugin.file_checker;


import junit.framework.TestCase;

import org.junit.BeforeClass;
import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;

public class CustomRepresenterTestCase extends TestCase{

	@BeforeClass
	public static void setUpBeforeClass() throws Exception {
	}

	
	public void testNatToDump() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(new CustomRepresenter(), new DumperOptions()),	new CustomResolver());
		
		Nat sampleNat = new Nat();
		sampleNat.setId("andy");
		
			
		String output = yaml.dump(sampleNat);
		// this test is affected by the resolver
		String properOutput="<andy=nat>\n";
		assertEquals(properOutput, output);
	}
}
