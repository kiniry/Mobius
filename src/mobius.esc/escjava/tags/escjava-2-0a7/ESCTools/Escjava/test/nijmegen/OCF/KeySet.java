class KeySet
{
    public static final byte MAX_KEYS = 3;

    private /*@ spec_public @*/ SecurityKey[] keyArray;

    /*@ 
      @ invariant // \elemtype(\typeof(keyArray)) == \type(SecurityKey) &&
      @           keyArray != null && keyArray.length == MAX_KEYS;
      @*/

    /*@ behavior
      @   requires 1 <= index && index <= MAX_KEYS;
      @ modifiable keyArray[index-1];
      @    ensures index >= 1;
      @    ensures index <= MAX_KEYS;
      @    ensures bArray != null;
      @    ensures bArray.length <= SecurityKey.MAX_KEY_LENGTH;
      @    ensures keyArray[index] != null;
      @    ensures keyArray[index].keyLen == bArray.length;
      @    ensures (\forall short i ; 0 <= i && i < keyArray[index].keyLen
      @                               ==> keyArray[index].theKey[i] == bArray[i]);
      @    signals (ArrayIndexOutOfBoundsException) false;
      @    signals (NullPointerException) false;
      @*/
    public void setKeyBytes(/*@ non_null @*/ byte[] bArray,
                            byte index)
    {
        keyArray[--index] = new SecurityKey();
        keyArray[index].setKey(bArray);
    }
}