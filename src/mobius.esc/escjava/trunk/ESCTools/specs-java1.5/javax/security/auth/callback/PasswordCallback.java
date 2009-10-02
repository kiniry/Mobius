package javax.security.auth.callback;

public class PasswordCallback implements Callback, java.io.Serializable {
    private static final long serialVersionUID = 2267422647454909926L;
    private String prompt;
    private boolean echoOn;
    private char[] inputPassword;
    
    public PasswordCallback(String prompt, boolean echoOn) {
        
        if (prompt == null || prompt.length() == 0) throw new IllegalArgumentException();
        this.prompt = prompt;
        this.echoOn = echoOn;
    }
    
    public String getPrompt() {
        return prompt;
    }
    
    public boolean isEchoOn() {
        return echoOn;
    }
    
    public void setPassword(char[] password) {
        this.inputPassword = (password == null ? null : (char[])(char[])password.clone());
    }
    
    public char[] getPassword() {
        return (inputPassword == null ? null : (char[])(char[])inputPassword.clone());
    }
    
    public void clearPassword() {
        if (inputPassword != null) {
            for (int i = 0; i < inputPassword.length; i++) inputPassword[i] = ' ';
        }
    }
}
