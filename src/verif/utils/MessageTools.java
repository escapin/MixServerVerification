package verif.utils;


public class MessageTools {

	/*@ public normal_behaviour
	  @ requires message != null;
	  @ ensures (\fresh(\result) && \dl_array2seq(\result) == \dl_array2seq(\old(message)));	  
	  @ assignable \nothing;
	  @*/
    public static /*@helper @*/ byte[] copyOf(byte[] message) {
        if (message==null) return null;
        byte[] copy = new byte[message.length];
        /*@ loop_invariant 0 <= i && i <= message.length
          @ 		&& copy != null && copy != message && \fresh(copy)
          @ 		&& copy.length == message.length
          @ 		&& (\forall int j; 0 <= j && j < i; copy[j] == message[j]);
          @ assignable copy[*];
          @ decreases message.length - i;
          @*/
        for (int i = 0; i < message.length; i++) {
        	copy[i] = message[i];
        }
        return copy;
    }
    /*@ public normal_behaviour
	  @ requires a != null && b!= null;
	  @ ensures \result <==> \dl_array2seq(a) == \dl_array2seq(b);	  
	  @ assignable \strictly_nothing;
	  @*/
    public static/*@helper@*/ boolean equal(byte[] a, byte[] b) {
        if (a != null && b != null) {
            if( a.length != b.length ) return false;
            /*@ loop_invariant 0 <= i && i <= a.length
            @ 		&& a != null && b != null
            @ 		&& a.length == b.length
            @ 		&& (\forall int j; 0 <= j && j < i; a[j] == b[j]);
            @ assignable \strictly_nothing;
            @ decreases a.length - i;
            @*/
            for( int i=0; i<a.length; ++i) {
                try {
                    if( a[i] != b[i] ) return false;
                } catch (Throwable t) {}
            }
            return true;
        } else {
            return false; // you can also return true here, I (the Joana guy) don't care
        }
    }

    public static byte[] getZeroMessage(int messageSize) {
        byte[] zeroVector = new byte[messageSize];
        for (int i = 0; i < zeroVector.length; i++) {
            zeroVector[i] = 0x00;
        }
        return zeroVector;
    }

    /**
     * Concatenates messages in a way that makes it possible to unambiguously
     * split the message into the original messages (it adds length of the
     * first message at the beginning of the returned message).
     */
    /*@ public behaviour
      @ diverges true;
      @ signals_only NullPointerException;
      @ ensures \typeof(\result) == \type(byte[])
      @ 	&& ((m1 != null && m2 != null)
      @ 		==> (\result.length == m1.length + m2.length + 4))
      @         && \fresh(\result);
      @ signals (NullPointerException e) true;
      @*/
    public static /*@ pure helper @*/ byte[] concatenate(/*@ nullable @*/ byte[] m1,
                                                         /*@ nullable @*/ byte[] m2) {
        // Concatenated Message --> byte[0-3] = Integer, Length of Message 1
        byte[] out = new byte[m1.length + m2.length + 4];

        // 4 bytes for length
        byte[] len = intToByteArray(m1.length);

        // copy all bytes to output array
        int j = 0;
        int i = 0;
        /*@ loop_invariant 0 <= i && len != null && out != null && m1 != null && m2 != null
          @             && \typeof(out) == \type(byte[]) && \typeof(len) == \type(byte[])
          @             && 0 <= j && j <= len.length && j <= out.length
          @             && len.length == 4 && out.length == m1.length + m2.length + 4
          @             && j == i;
          @ assignable out[*], j;
          @ decreases len.length - i;
          @*/
        for( i=0; i<len.length; ++i ) out[j++] = len[i];
        /*@ loop_invariant 0 <= i && m1 != null && out != null && m1 != null && m2 != null
          @             && \typeof(out) == \type(byte[]) && \typeof(len) == \type(byte[])
          @             && 4 <= j && j <= m1.length + 4 && j <= out.length
          @             && out.length == m1.length + m2.length + 4
          @             && j == i + 4;
          @ assignable out[*], j;
          @ decreases m1.length - i;
          @*/
        for( i=0; i<m1.length;  ++i ) out[j++] = m1[i];
        /*@ loop_invariant 0 <= i && m2 != null && out != null && m1 != null && m2 != null
          @             && \typeof(out) == \type(byte[]) && \typeof(len) == \type(byte[])
          @             && m1.length + 4 <= j && j <= m2.length + m1.length + 4 && j <= out.length
          @             && out.length == m1.length + m2.length + 4
          @             && j == i + m1.length + 4;
          @ assignable out[*], j;
          @ decreases m2.length - i;
          @*/
        for( i=0; i<m2.length;  ++i ) out[j++] = m2[i];

        return out;
    }

    /**
     * Simply concatenates the messages (without adding any information for
     * de-concatenation).
     */
    public static byte[] raw_concatenate(byte[] a, byte[] b) {
        byte[] result = new byte[a.length + b.length];
        int j = 0;
        for( int i=0; i<a.length; ++i ) result[j++] = a[i];
        for( int i=0; i<b.length; ++i ) result[j++] = b[i];
        return result;
    }

    /**
     * Projection of the message to its two parts (part 1 = position 0, part 2 = position 1) Structure of the expected data: 1 Byte Identifier [0x01], 4 Byte
     * length of m1, m1, m2
     */
    /*@ private normal_behaviour
      @ ensures \fresh(\result);
      @*/
    private static /*@ pure helper @*/ byte[] project(/*@ nullable @*/ byte[] message, int position) {
        try {
            int len = byteArrayToInt(message);
            if (len > (message.length - 4)) return new byte[]{}; // Something is wrong with the message!
            if (position == 0) {
                byte[] m1 = new byte[len];
                /*@ loop_invariant 0 <= i && i <= len && \fresh(m1) && m1 != len
                  @ 		&& m1.length == len && len <= message.length - 4
                  @ 		&& (\forall int j; 0 <= j && j < i; m1[j] == message[j + 4]);
                  @ assignable m1[*];
                  @ decreases len - i;
                  @*/
                for (int i = 0; i < len; i ++) m1[i] = message[i + 4];
                return m1;
            } else if (position == 1) {
                byte[] m2 = new byte[message.length - len - 4];
                /*@ loop_invariant 0 <= i && i <= message.length - len - 4 && \fresh(m2)
                  @ 		&& m2 != len && m2.length == message.length - len - 4
                  @ 		&& len <= message.length - 4
                  @ 		&& (\forall int j; 0 <= j && j < i; m2[j] == message[j + 4 + len]);
                  @ assignable m2[*];
                  @ decreases message.length - len - 4 - i;
                  @*/
                for (int i = 0; i < message.length - len - 4; i ++) m2[i] = message[i + 4 + len];
                return m2;
            } else return new byte[]{};
        } catch (Exception e) {
            return new byte[]{};
        }
    }

    /*@ private normal_behaviour
      @ ensures \fresh(\result);
      @*/
    public static /*@ pure helper @*/ byte[] first(/*@ nullable @*/ byte[] in) {
        return project(in, 0);
    }

    /*@ private normal_behaviour
      @ ensures \fresh(\result);
      @*/
    public static /*@ pure helper @*/ byte[] second(/*@ nullable @*/ byte[] in) {
        return project(in, 1);
    }
    /**
     * Transforms a 4 byte array back to int. 
     * Since bitwise operators are not sufficiently supported 
     * in KeY, I have replaced them with other operators. 
     */
    /*@ public normal_behaviour
      @ requires b.length >= 4;
      @ ensures \result == 256 * 256 * 256 * unsign(b[0]) + 256 * 256 * unsign(b[1])+ 256 * unsign(b[2])+ unsign(b[3]);
      @*/
    public static final /*@ pure helper @*/ int byteArrayToInt(byte [] b) {
    	int result = 0;
    	result += 256 * 256 * 256 * unsign(b[0]);
    	result += 256 * 256 * unsign(b[1]);
    	result += 256 * unsign(b[2]);
    	result += unsign(b[3]);
    	return result;   	

    	
//        return (b[0]  << 24)
//                + ((b[1] & 0xFF) << 16)
//                + ((b[2] & 0xFF) << 8)
//                + (b[3] & 0xFF);
    }
    /**
     * Transforms a signed byte value (range -128 to 127) to an unsigned 
     * byte value (range 0 to 255).         
     */      
    /*@
      public normal_behaviour
      ensures \result == (b < 0 ? b + 256 : b);
      assignable \strictly_nothing;
     @*/
    public static final int /*@pure helper@*/ unsign(byte b){
    	if(b<0){
    		return (int) b + 256;
    	}
    	return b;
    }
    
    /**
	 * Model method (lemma) stating that if a is the representation of value,
     * then byteArrayToInt will return value value. We need to make an additional 
     * assumption that value is less than or equal to int_MAX otherwise a 4 byte 
     * array will not be enough to store value and the higher bytes of data would 
     * be lost.
	 */
	/*@
	  requires value >= 0;
	  requires value <= \dl_int_MAX;	  
	  requires isByteArrOfInt(a,value);
	  ensures byteArrayToInt(a) == value;
	  ensures \result;
	  public static model boolean reverseByteArrOfInt2(byte[] a, int value){
	     return true;
	  }
	 @*/
    /**
     * Model method (lemma) stating that if a is the representation of value,
     * then byteArrayToInt will return value value. This lemma has been proven using 
     * the Java Integer Semantics(ass opposed to the default KeY Integer Semantics) since in
     * this semantics value will automatically be less than or equal to int_MAX. The model method
     * reverseByteArrOfInt2 is used in the proof.
     */
    /*@
	  requires value >= 0;	  	  
	  requires isByteArrOfInt(a,value);
	  ensures byteArrayToInt(a) == value;
	  ensures \result;
	  public static model boolean reverseByteArrOfInt(byte[] a, int value){
	     return true;
	  }
	 @*/
    /**
     * Model method which returns true if the first 4 bytes of byte array a
     * are the representation of int value value.
     */
    /*@	
      public model_behaviour 
      requires value >= 0;           
	  ensures \result ==> a.length >= 4;	       
      ensures \result ==> a[0] == (byte)((value / 256 / 256 / 256) % 256);
      ensures \result ==> a[1] == (byte)((value / 256 / 256) % 256);
      ensures \result ==> a[2] == (byte)((value / 256) % 256);
      ensures \result ==> a[3] == (byte)(value % 256);	  
	  public static model boolean isByteArrOfInt(byte[] a, int value){
	     return a.length >= 4 && a[0] == (byte)((value / 256 / 256 / 256) % 256) && 
	             a[1] == (byte)((value / 256 / 256) % 256) && a[2] == (byte)((value / 256) % 256)
	             && a[3] == (byte)(value % 256);
	  }
	 @*/   

    /**
     * Transforms an int value into a 4 byte array. 
     * We require that the value is greater or equal to 0.
     * Since bitwise operators are not sufficiently supported 
     * in KeY, I have replaced them with other operators.      
     */
    /*@ 
       public normal_behaviour
       requires value >= 0;
       ensures isByteArrOfInt(\result, value);
       ensures \fresh(\result); 
      @*/
    public static final /*@ pure helper @*/ byte[] intToByteArray(int value) {    	
    	byte[] result = new byte[4];
    	result[3] = (byte) (value % 256);
    	
    	result[2] = (byte) ((value / 256) % 256);
    	
    	result[1] = (byte) ((value / 256 / 256) % 256);
    	
    	result[0] = (byte) ((value / 256 / 256 / 256) % 256);    	
    	return result;
//        return new byte[] {
//                (byte)(value >>> 24),
//                (byte)(value >>> 16),
//                (byte)(value >>> 8),
//                (byte)value};
    }
    
    /*@ public normal_behaviour
      @ ensures \result.length == 8 && \fresh(\result);
      @*/
    public static final /*@ pure helper @*/ byte[] longToByteArray(long value) {
        byte[] b = new byte[8];
        /*@ loop_invariant 0 <= i && b != null && b.length == 8;
          @ assignable b[*];
          @ decreases b.length - i;
          @*/
        for (int i = 0; i < b.length; i++) {
            int offset = (b.length - 1 - i) * 8;
            b[i] = (byte) ((value >>> offset) & 0xFF);
        }
        return b;
    }

    public static final long byteArrayToLong(byte [] b){
        long value=0;
        for(int i=0; i<b.length; i++){
            int offset=(b.length -1 - i) * 8;
            value += (long) (b[i] & 0xFF) << offset;
        }
        return value;
    }
}