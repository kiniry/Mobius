import java.util.Properties;

class mainRpcSammy {

    public static void main(String[] args) {

	Sammy sammy = new Sammy(true);

	sammy.start_prover();
	
	try { Thread.sleep(3); }
	catch (Exception e){ System.out.println(e);}

	Properties p = new Properties();

	// test to sets a flag
	p.setProperty("",""); // has no sense, but do not crash everything
	p.setProperty("-timeout","1000");
	p.setProperty("-max_instances","5");
	p.setProperty("-exhaustive","");

	sammy.set_prover_resource_flags(p);
	
	sammy.stop_prover();
    
    }

}
