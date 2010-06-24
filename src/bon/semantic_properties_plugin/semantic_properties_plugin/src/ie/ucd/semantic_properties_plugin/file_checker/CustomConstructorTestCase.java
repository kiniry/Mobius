package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.Map;

import junit.framework.TestCase;

import org.yaml.snakeyaml.Dumper;
import org.yaml.snakeyaml.DumperOptions;
import org.yaml.snakeyaml.Loader;
import org.yaml.snakeyaml.Yaml;


public class CustomConstructorTestCase extends TestCase{
	
	public void testNatConstructor() {
		Yaml yaml = new Yaml(new Loader(new CustomConstructor()), new Dumper(
				new CustomRepresenter(), new DumperOptions()),
				new CustomResolver());
		Nat sampleNat= new Nat("example",0);
		Object data = yaml.load("{samples: !nat '<example=nat>'}");
		Map<String, Nat> map = (Map<String, Nat>) data;
		
		assertEquals(sampleNat, map.get("samples"));

	}

}
