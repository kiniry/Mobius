package ie.ucd.semantic_properties_plugin.file_checker;

import java.util.Map;

import org.yaml.snakeyaml.constructor.Constructor;
import org.yaml.snakeyaml.constructor.AbstractConstruct;
import org.yaml.snakeyaml.nodes.MappingNode;
import org.yaml.snakeyaml.nodes.Node;
import org.yaml.snakeyaml.nodes.ScalarNode;
import org.yaml.snakeyaml.nodes.SequenceNode;
import org.yaml.snakeyaml.nodes.Tag;

public class CustomConstructor extends Constructor {
    public CustomConstructor() {
        this.yamlConstructors.put(new Tag("!nat"),new ConstructNat());
    }

    private class ConstructNat extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            Nat temp=new Nat();
            temp.setId(a);
            return temp;
        }
    }
}