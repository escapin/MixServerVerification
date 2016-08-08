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
    
    /*@
      public model_behaviour
	  requires offset >= 0;
	  requires offset + b.length < a.length;  
	  ensures  \result ==> (\forall int i; 0 <= i && i < b.length; b[i] == a[offset+i]);
	  public static model boolean isIdentical(byte[] a, byte[] b, int offset){
	     return (\forall int i; 0 <= i && i < b.length; b[i] == a[offset+i]);
	  }
	 @*/

    /**
     * Concatenates messages in a way that makes it possible to unambiguously
     * split the message into the original messages (it adds length of the
     * first message at the beginning of the returned message).
     */
    /*@ 
      public normal_behaviour      
      ensures \result.length == m1.length + m2.length + 4; 
      ensures isByteArrOfInt(\result, m1.length);
      ensures isIdentical(\result, m1, 4); 
      ensures isIdentical(\result, m2, 4 + m1.length);   
      ensures \fresh(\result);     
      @*/
    public static /*@ pure helper @*/ byte[] concatenate( byte[] m1,
                                                          byte[] m2) {
        // Concatenated Message --> byte[0-3] = Integer, Length of Message 1
    	int length = m1.length + m2.length + 4;
        byte[] out = new byte[length];

        // 4 bytes for length
        byte[] len = intToByteArray(m1.length);

        // copy all bytes to output array
        int j = 0;
        int i = 0;
        /*@
         loop_invariant 0 <= i && i <= len.length;
         loop_invariant j == i;
         loop_invariant (\forall int k; 0 <= k && k < i; len[k] == out[k]);
         loop_invariant isByteArrOfInt(len, m1.length);
         loop_invariant len.length == 4 && out.length == m1.length + m2.length + 4;
         assignable out[0..3];
         decreases len.length - i;
         @*/
        for( i=0; i<len.length; ++i ) out[j++] = len[i];
        /*@
        loop_invariant 0 <= i && i <= m1.length;
        loop_invariant j == i + 4;
        loop_invariant (\forall int k; 0 <= k && k < i; m1[k] == out[k+4]);
        loop_invariant isByteArrOfInt(len, m1.length);
        loop_invariant isByteArrOfInt(out, m1.length);
        loop_invariant len.length == 4 && out.length == m1.length + m2.length + 4;
        assignable out[4..3+m1.length];
        decreases m1.length - i;
        @*/
        for( i=0; i<m1.length;  ++i ) out[j++] = m1[i];
        /*@
        loop_invariant 0 <= i && i <= m2.length;
        loop_invariant j == i + 4 + m1.length;
        loop_invariant (\forall int k; 0 <= k && k < i; m2[k] == out[k+4+m1.length]);
        loop_invariant isByteArrOfInt(len, m1.length);
        loop_invariant isByteArrOfInt(out, m1.length);
        loop_invariant isIdentical(out, m1, 4);
        loop_invariant len.length == 4 && out.length == m1.length + m2.length + 4;
        assignable out[4+m1.length..out.length];
        decreases m2.length - i;
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
    
    private static /*@ pure helper @*/ byte[] project(byte[] message, int position) {
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

    /*@ public normal_behaviour
        requires in.length >= 4 + byteArrayToInt(in);
        requires byteArrayToInt(in) >= 0;
        ensures isIdentical(in,\result,4);
        ensures \result.length == byteArrayToInt(in);
        ensures \fresh(\result);
    @*/
    public static /*@ pure helper @*/ byte[] first(byte[] in) {
    	try{
    		int len = byteArrayToInt(in);
        	if (len < 0 || len > (in.length - 4)) return new byte[]{}; // Something is wrong with the message!
        	
        	byte[] m1 = new byte[len];
            /*@ loop_invariant 0 <= i && i <= len && \fresh(m1) && m1 != len
              @ 		&& m1.length == len && len <= in.length - 4 && len == byteArrayToInt(in)
              @ 		&& (\forall int j; 0 <= j && j < i; m1[j] == in[j + 4]);
              @ assignable m1[*];
              @ decreases len - i;
              @*/
            for (int i = 0; i < len; i ++){
            	m1[i] = in[i + 4];
            }
            return m1;
    	}catch(Exception e){
    		return new byte[]{};
    	} 
    	
        //return project(in, 0);
    }

    /*@ public normal_behaviour      
      requires in.length >= 4 + byteArrayToInt(in);
      requires byteArrayToInt(in) >= 0;
      ensures isIdentical(in,\result,4 + byteArrayToInt(in));
      ensures \result.length == in.length -byteArrayToInt(in)-4;
      ensures \fresh(\result);
      @*/
    public static /*@ pure helper @*/ byte[] second(byte[] in) {
    	try{
    		int len = byteArrayToInt(in);
        	if (len < 0 || len > (in.length - 4)) return new byte[]{}; // Something is wrong with the message!
        	
        	byte[] m2 = new byte[in.length - len - 4];
            /*@ loop_invariant 0 <= i && i <= in.length - len - 4 && \fresh(m2)
              @ 		&& m2 != len && m2.length == in.length - len - 4
              @ 		&& len <= in.length - 4
              @ 		&& (\forall int j; 0 <= j && j < i; m2[j] == in[j + 4 + len]);
              @ assignable m2[*];
              @ decreases in.length - len - 4 - i;
              @*/
            for (int i = 0; i < in.length - len - 4; i ++) m2[i] = in[i + 4 + len];
            return m2;
    	}catch(Exception e){
    		return new byte[]{};
    	}   	
        
        //return project(in, 1);
    }
    /**
     * Transforms a 4 byte array back to int. 
     * Since bitwise operators are not sufficiently supported 
     * in KeY, I have replaced them with other operators. 
     */
    /*@ public normal_behaviour
      @ requires b.length >= 4;
      @ ensures \result == 256 * 256 * 256 * unsign(b[0]) + 256 * 256 * unsign(b[1])+ 256 * unsign(b[2])+ unsign(b[3]);
      @ also
      @ public normal_behaviour
      @ requires b.length >= 4;
      @ ensures \result == byteArrayToInt(b);
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
	  accessible a, value;
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
       ensures \result.length == 4;
       ensures \fresh(\result); 
       accessible value;
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