package custom_yaml;

import java.util.Map;

import org.yaml.snakeyaml.constructor.Constructor;
import org.yaml.snakeyaml.constructor.AbstractConstruct;
import org.yaml.snakeyaml.nodes.MappingNode;
import org.yaml.snakeyaml.nodes.Node;
import org.yaml.snakeyaml.nodes.ScalarNode;
import org.yaml.snakeyaml.nodes.SequenceNode;
import org.yaml.snakeyaml.nodes.Tag;

import semantic_properties_plugin.custom_objects.*;
public class CustomConstructor extends Constructor {
    public CustomConstructor() {
        this.yamlConstructors.put(new Tag("!nat"),new ConstructNat());
        this.yamlConstructors.put(new Tag("!myint"),new ConstructMyInt());
        this.yamlConstructors.put(new Tag("!myfloat"),new ConstructMyFloat());
        this.yamlConstructors.put(new Tag("!myclass"),new ConstructMyClass());
        this.yamlConstructors.put(new Tag("!mydate"),new ConstructMyDate());
        this.yamlConstructors.put(new Tag("!mydescription"),new ConstructMyDescription());
        this.yamlConstructors.put(new Tag("!myemail"),new ConstructMyEmail());
        this.yamlConstructors.put(new Tag("!myexpression"),new ConstructMyExpression());
        this.yamlConstructors.put(new Tag("!mythrowable"),new ConstructMyThrowable());
        this.yamlConstructors.put(new Tag("!myurl"),new ConstructMyURL());
        this.yamlConstructors.put(new Tag("!myversion"),new ConstructMyVersion());
        this.yamlConstructors.put(new Tag("!mystring"),new ConstructMyString());
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

    private class ConstructMyInt extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyInt temp=new MyInt();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyFloat extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyFloat temp=new MyFloat();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyClass extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyClass temp=new MyClass();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyDate extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyDate temp=new MyDate();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyDescription extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyDescription temp=new MyDescription();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyEmail extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyEmail temp=new MyEmail();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyExpression extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyExpression temp=new MyExpression();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyString extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyString temp=new MyString();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyThrowable extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyThrowable temp=new MyThrowable();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyURL extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyURL temp=new MyURL();
            temp.setId(a);
            return temp;
        }
    }
    private class ConstructMyVersion extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            int position = val.indexOf('=');
            String a = (val.substring(1, position));     
            MyVersion temp=new MyVersion();
            temp.setId(a);
            return temp;
        }
    }
}