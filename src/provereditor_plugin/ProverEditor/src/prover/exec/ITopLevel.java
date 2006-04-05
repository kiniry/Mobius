package prover.exec;

public interface ITopLevel {
	public void sendCommand(String s) throws AProverException;
	public void clearBuffer();
	public boolean isAlive();
	public String getBuffer();
	public void stop();
	public void addStreamListener(IStreamListener isl);
	public void removeStreamListener(IStreamListener isl);
	public boolean isProofMode();
	public void undo(int steps) throws AProverException;
	public void doBreak() throws AProverException;
}
