package Ambit;

import java.applet.*;

class Main
{
  public static void main(String[] args)
    {
      Applet a = new AmbitApplet();
      a.init();
      a.start();
      a.handleEvent(null);
      a.stop();
      a.destroy();
    }
}


  
