package ie.ucd.semanticproperties.plugin.yaml;

import ie.ucd.semanticproperties.plugin.customobjects.*;

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
          MyObject temp =  convertNode(node);
          String a = temp.getId();
          Integer b = Integer.valueOf((String)temp.getValue());
          return new MyInt(a,b);

        }
    }
    private class ConstructMyFloat extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
        	MyObject temp =  convertNode(node);
          String a = temp.getId();
          Float b = Float.valueOf((String)temp.getValue());
          return new MyFloat(a,b);
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
            MyObject temp = convertNode(node);
            String a = temp.getId();
            String b= (String) temp.getValue();
            return new MyDescription(a,b.substring(0,b.length()-1));
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
          MyObject temp =  convertNode(node);
          String a = temp.getId();
          String b = (String) temp.getValue();
          return new MyExpression(a,b.substring(1,b.length()-1));
        }
    }
    private class ConstructMyString extends AbstractConstruct {
        @SuppressWarnings("unchecked")
        public Object construct(Node node) {
        	String val = (String) constructScalar((ScalarNode) node);
            MyObject temp =  convertNode(node);
            String a = temp.getId();
            String b = (String) temp.getValue();
            return new MyString(a,b.substring(1,b.length()-1));
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
          MyObject temp =  convertNode(node);
          String a = temp.getId();
          Float b = Float.valueOf((String)temp.getValue());
          return new MyVersion(a,b);

        }
    }
    /**
     * Method to concert a Node into generalMyObject.
     * @param node
     * @return
     */
    public MyObject convertNode(Node node){
      String val = (String) constructScalar((ScalarNode) node);
      int position = val.indexOf('=');
      String a = (val.substring(1, position));
      int position2 = val.indexOf('=', position+1);
      String b = (val.substring(position2+1,val.length()-1));
      return new MyObject(a,b);
    }
}