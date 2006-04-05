package prover.exec;

public interface ITopLevel {
	public ITopLevel createTopLevel (String strCoqTop, String [] path) throws AProverException;
	public void sendCommand(String s) throws AProverException;
	public void clearBuffer();
	public boolean isAlive();
	public String getBuffer();
	public void stop();
	public void addListener(IStreamListener isl);
	public void removeListener(IStreamListener isl);
	public boolean isProofMode();
	public void undo(int steps) throws AProverException;
	public void doBreak() throws AProverException;
}
