package ie.ucd.semantic_properties_plugin.file_checker;

import org.yaml.snakeyaml.nodes.Node;
import org.yaml.snakeyaml.nodes.Tag;
import org.yaml.snakeyaml.representer.Represent;
import org.yaml.snakeyaml.representer.Representer;

public class CustomRepresenter extends Representer {
    public CustomRepresenter() {
        this.representers.put(Nat.class, new RepresentNat());
        
    }

    private class RepresentNat implements Represent {
        public Node representData(Object data) {
            Nat nat = (Nat) data;
            String value = "<"+nat.getId()+"=nat>";
            return representScalar(new Tag("!nat"), value);
        }
    }
}