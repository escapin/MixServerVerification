package verif.selectvoting.system.core;

import verif.selectvoting.system.core.MixServer.MalformedData;
import verif.selectvoting.system.core.MixServer.ServerMisbehavior;
import verif.environment.Environment;
import verif.functionalities.pkienc.Decryptor;
import verif.functionalities.pkienc.Encryptor;
import verif.functionalities.pkisig.Signer;
import verif.functionalities.pkisig.Verifier;
import verif.utils.MessageTools;

public final class Setup {

	// PURE SUPPORT METHODS:
	
	/**
	 * Returns a new array which is sorted and a permutation of entr_arr.
	 */
	/*@
	  public normal_behaviour
	  ensures \dl_seqPerm(\dl_array2seq2d(\result), \dl_array2seq2d(entr_arr));
	  ensures (\forall int i; 0 <= i && i < \result.length-1; Utils.compare(\result[i],\result[i+1]) <= 0);	
	  ensures \fresh(\result);
	  assignable \nothing;	    
	@*/	
	private static /*@helper@*/byte[][] sort(byte[][] entr_arr) {
		
		byte[][] result = Utils.copyOf(entr_arr);
		
		if (result != null) {
			Utils.sort(result, 0, result.length);
			return result;
		} else {
			return new byte[][] {};
		}
	}
    /**
     * Returns true if and only if arr1 and arr2 are permutations of each other. 
     */
    /*@ public normal_behaviour  
        requires arr1 != null && arr2 != null;    
        ensures \result <==> \dl_seqPerm(\dl_array2seq2d(arr1), \dl_array2seq2d(arr2));
        assignable \nothing;
      @*/
	private static /*@helper@*/ boolean setEquality(byte[][] arr1, byte[][] arr2) {
		if(arr1.length!=arr2.length) return false;
		byte[][] a1=sort(arr1);
		byte[][] a2=sort(arr2);		
		return equals(a1, a2);
	}
	/**
     * Returns true if and only if a1 and a2 are copies of each other. 
     */
    /*@
      public normal_behaviour
      requires a1 != null && a2 != null;
      requires a1.length == a2.length;
      ensures \result == (\dl_array2seq2d(a1) == \dl_array2seq2d(a2));
      assignable \strictly_nothing;
     @*/
	private static /*@helper@*/ boolean equals(byte[][] a1, byte[][] a2) {
		/*@ loop_invariant 0 <= i && i <=a1.length && a1.length == a2.length;
            loop_invariant  (\forall int j; 0 <= j && j < i; \dl_array2seq(a1[j]) == \dl_array2seq(a2[j]));          
            assignable \strictly_nothing;
            decreases a1.length - i;
        @*/
		for(int i=0;i<a1.length;i++){
			if(!MessageTools.equal(a1[i],a2[i])) {
				return false;
			}
		}				
		return true;
	}
	
	// MAIN METHOD:
	
	// one secret bit
	private static/*@spec_public@*/ boolean secret; // the HIGH value
	
	
	public static void main (String[] a) throws Throwable {

		// SETUP THE COMPONENTS

        byte[] electionID = Environment.untrustedInputMessage();

		// create the cryptographic functionalities
		Decryptor mixDecr = new Decryptor();
		Encryptor mixEncr = mixDecr.getEncryptor();
		Signer mixSign = new Signer();
		
		Signer precServSign = new Signer();
		Verifier precServVerif = precServSign.getVerifier(); 

		main2(mixDecr, mixEncr, mixSign, precServSign, precServVerif, electionID);
		
	}
	/**
	 *  KeY: This method checks a message array to see if the array and its elements are not null and if the length
	 *  of the array and of its elements are equal to numberOfMessages and lengthOfMessages respectively.
	 *  If any of these conditions are not fulfilled a Throwable is thrown.
	 *  By using method we ensure that the preconditions for the other methods(not null and messages of equal lengths) 
	 *  are fulfilled.
	 */
	
	/*@
    public exceptional_behaviour
    requires msg==null || msg.length != numberOfMessages || (\exists int i; 0<=i && i < msg.length; msg[i] == null || msg[i].length != lengthOfMessages);
    signals(Throwable);
    
    also
    
    public normal_behaviour
    requires msg != null;
    requires msg.length == numberOfMessages;
    requires (\forall int i; 0<=i && i < msg.length; msg[i]!= null && msg[i].length == lengthOfMessages);
    ensures true;           
    assignable \strictly_nothing;
  @*/
	private static /*@helper@*/void checkMessages(/*@nullable@*/byte[][] msg, int numberOfMessages, int lengthOfMessages) throws Throwable{
		
		if(msg==null || msg.length != numberOfMessages){
			throw new Throwable();
		}
		/*@
		  loop_invariant 0 <= i && i <= numberOfMessages;
		  loop_invariant numberOfMessages == msg.length;
		  loop_invariant (\forall int j; 0 <= j && j < i; msg[j] != null && msg[j].length == lengthOfMessages);
		  assignable \strictly_nothing;
		  decreases numberOfMessages - i;
		 @*/
		for(int i=0; i<numberOfMessages; ++i){	
			/**
			 * KeY: Added explicit check for null, otherwise it would have thrown a NullPointerException when checking the length.
			 * In any case null messages are not allowed.
			 */
			if(msg[i] == null){
				throw new Throwable();
			}
			
			if(msg[i].length != lengthOfMessages)
				throw new Throwable();
		}		
		
	}


    private static void main2(Decryptor mixDecr, Encryptor mixEncr, Signer mixSign,
                              Signer precServSign, Verifier precServVerif, byte[] electionID)
                                      throws Throwable, MalformedData, ServerMisbehavior {
		MixServer mixServ = 
				new  MixServer(mixDecr, mixSign, precServVerif, electionID);

		// let the adversary choose how many messages have to 
		// be sent to the mix server
		int numberOfMessages = Environment.untrustedInput();
		
		// let the adversary decide the length of the messages 
		// all the messages must have the same length: 
		int lengthOfTheMessages = Environment.untrustedInput();
		
		
		// let the environment determine the two arrays of messages
		byte[][] msg1 = new byte[numberOfMessages][];
		byte[][] msg2 = new byte[numberOfMessages][];
		for(int i=0; i<numberOfMessages; ++i){
			msg1[i] = Environment.untrustedInputMessage();
			msg2[i] = Environment.untrustedInputMessage();
			
		}
		
		checkMessages(msg1, numberOfMessages, lengthOfTheMessages);
		checkMessages(msg2, numberOfMessages, lengthOfTheMessages);
		
		byte[][] chosen = chooseAndStoreMsg(msg1, msg2);
		
		innerMain(mixEncr, precServSign, electionID, mixServ, numberOfMessages,
		          lengthOfTheMessages, chosen);
    }
    /**
     * If msg1 and msg2 are not permutations of each other a Throwable is thrown.
     * 
     * If they are permutations and if all messages are of equal length(established by the checkMsg method)
     * the result of this method is a copy of msg1 if secret is set and a copy of msg2 otherwise, and in 
     * ConservativeExtension.messages we always store a copy of msg1.
     * 
     */
    /*@
       public exceptional_behaviour
       requires !\dl_seqPerm(\dl_array2seq2d(msg1), \dl_array2seq2d(msg2));
       signals(Throwable);
       
       also
       
       public normal_behaviour
       requires (\forall int i; 0 <= i && i <= msg1.length; msg1[i].length == msg2[i].length);
       requires \dl_seqPerm(\dl_array2seq2d(msg1), \dl_array2seq2d(msg2));
       ensures \dl_array2seq2d(ConservativeExtension.messages) == \dl_array2seq2d(msg1);
       ensures secret ==> \dl_array2seq2d(\result) == \dl_array2seq2d(msg1);
       ensures !secret ==> \dl_array2seq2d(\result) == \dl_array2seq2d(msg2);       
       assignable ConservativeExtension.messages;
     @*/
	private static /*@helper@*/ byte[][] chooseAndStoreMsg(byte[][] msg1, byte[][] msg2) throws Throwable {
		// the two vectors must be two permutations of the same set
		if(!setEquality(msg1, msg2)){
			throw new Throwable();
		}
		
		ConservativeExtension.storeMessages(msg1);
		
		byte[][] chosen = chooseMsg(msg1, msg2);
		
		return chosen;
	}
    
    //@public static ghost MixServer mix;

	/* @public normal_behaviour 
	   requires asAMessage == mixServ.concatenated;
	   ensures \dl_array2seq(mixServ.unsigned) == \dl_mConcat(\dl_array2seq(Tag.BALLOTS), \dl_mConcat(\dl_array2seq(this.electionID), \dl_array2seq(mixServ.concatenated)));
	   assignable  mixServ.unsigned;
	@*/
    private static void innerMain(Encryptor mixEncr, Signer precServSign, byte[] electionID, MixServer mixServ,
                                  int numberOfMessages, int lengthOfTheMessages, byte[][] chosen)
                    throws MalformedData, ServerMisbehavior {
    	
    	
 	    byte[] signedInput = prepareInput(mixEncr, precServSign, electionID, chosen);

		
		
		// MODEL THE NETWORK
		
		// send the message over the network, controlled by the adversary
		Environment.untrustedOutputMessage(signedInput);
		
		// retrieve the message from the network
		byte[] mixServerInput=Environment.untrustedInputMessage();
		// what I get from the network is supposed to be the the message I sent (signedInput)
		// otherwise, if the message is not on the supposed format the mix server will 
		// throw an exception
		
		
		// let the mix server process the ballots 
		byte[] mixServerOutput=mixServ.processBallots(mixServerInput);
		
		
		// send the output of the mix server over the network
		Environment.untrustedOutputMessage(mixServerOutput);
    }
	private static byte[] prepareInput(Encryptor mixEncr, Signer precServSign, byte[] electionID,
			byte[][] chosen) {
		//@set mix.chosen = chosen;
    	byte[][] encrMsg = encryptMessages(mixEncr, electionID, chosen);			
    	//@set mix.encrypted = encrMsg;
		Utils.sort(encrMsg, 0, encrMsg.length);
		/*@set mix.sorted = encrMsg;@*/
		byte[] asAMessage = concatenateMessages(encrMsg);
		//@set mix.concatenated = asAMessage;
		byte[] signedInput = idTagSignMessages(precServSign, electionID, asAMessage);
		
		return signedInput;
	}
	/*@public normal_behaviour 
	   requires Tag.BALLOTS != null && mix != null;
	   requires asAMessage == mix.concatenated;
	   ensures \dl_array2seq(mix.unsigned) == \dl_mConcat(\dl_array2seq(Tag.BALLOTS), \dl_mConcat(\dl_array2seq(electionID), \dl_array2seq(mix.concatenated)));
	   assignable  mix.unsigned;
	@*/
	private static /*@helper@*/ byte[] idTagSignMessages(Signer precServSign, byte[] electionID, byte[] asAMessage) {
		//5
		// add election id, tag and sign
		byte[] elID_ballots = MessageTools.concatenate(electionID, asAMessage);		
		//6
		byte[] input = MessageTools.concatenate(Tag.BALLOTS, elID_ballots);
		//@set mix.unsigned = input;
		byte[] signatureOnInput = precServSign.sign(input);

		byte[] signedInput = MessageTools.concatenate(input, signatureOnInput);
		return signedInput;
	}
	/*@public normal_behaviour 
	   requires mix != null && mix.sorted != null;
	   requires encrMsg == mix.sorted;
	   ensures \dl_array2seq(\result) == \dl_mConcat(\dl_int2seq(mix.sorted.length), \dl_arrConcat(0, \dl_array2seq2d(mix.sorted)));
	   ensures \fresh(\result);
	   assignable \nothing;
	@*/
	private static /*@ helper @*/byte[] concatenateMessages(byte[][] encrMsg) {
		byte[] asAMessage=Utils.concatenateMessageArray(encrMsg);
		asAMessage=MessageTools.concatenate(MessageTools.intToByteArray(encrMsg.length), asAMessage);
		return asAMessage;
	}
	
	private static byte[][] encryptMessages(Encryptor mixEncr, byte[] electionID, byte[][] chosen) {
		//1
    	byte[][] idMsg = addIdToMsg(electionID, chosen);
		//2
		byte[][] encrMsg = encryptMsg(mixEncr, idMsg);
		return encrMsg;
	}
    
    
	private static byte[][] encryptMsg(Encryptor mixEncr, byte[][] idMsg) {
		byte[][] encrMsg = new byte[idMsg.length][];
		for(int i=0; i<idMsg.length; ++i){
			encrMsg[i] = mixEncr.encrypt(idMsg[i]);
		}
		return encrMsg;
	}
	
	/*@public normal_behaviour	   
	   ensures \result.length == chosen.length;
	   ensures (\forall int i; 0 <= i && i < \result.length; \dl_array2seq(\result[i]) == \dl_mConcat(\dl_array2seq(electionID), \dl_array2seq(chosen[i])));
	   ensures \fresh(\result);
	   assignable \nothing;
	@*/
	private static/*@helper@*/ byte[][] addIdToMsg(byte[] electionID, byte[][] chosen) {
		byte[][] idMsg = new byte[chosen.length][];
		/*@
		loop_invariant 0 <= i && i <= chosen.length && idMsg.length == chosen.length;
		loop_invariant (\forall int j; 0 <=j && j < i; \dl_array2seq(idMsg[j]) == \dl_mConcat(\dl_array2seq(electionID), \dl_array2seq(chosen[j])));
		loop_invariant (\forall int j; 0 <=j && j < i; idMsg[j] != null);
		assignable idMsg[*];
		decreases chosen.length - i;
		@*/
    	for(int i=0; i<chosen.length; ++i){
			idMsg[i] = MessageTools.concatenate(electionID, chosen[i]);
		}
		return idMsg;
	}
    /**
     *If secret is set returns a copy of msg1 otherwise returns a copy of msg2.     
     */
    /*@
    public normal_behaviour
    requires msg1 != null && msg2 != null && msg1.length == msg2.length;
    requires (\forall int i; 0 <= i && i <= msg1.length; msg1[i].length == msg2[i].length);       
    ensures secret ==> \dl_array2seq2d(\result) == \dl_array2seq2d(msg1);
    ensures !secret ==> \dl_array2seq2d(\result) == \dl_array2seq2d(msg2);
    ensures \fresh(\result);
    assignable \nothing;
   @*/
	private static/*@helper@*/ byte[][] chooseMsg(byte[][] msg1, byte[][] msg2) {
		byte[][] chosen = new byte[msg1.length][];
		/*@
	      loop_invariant 0 <= i && i <= chosen.length 
	      && chosen.length == msg1.length && msg1.length == msg2.length
	      && msg1 != chosen && msg2 != chosen && chosen !=null;
	      loop_invariant (\forall int j; 0 <= j && j < i; secret ==> \dl_array2seq(chosen[j]) == \dl_array2seq(msg1[j]));
	      loop_invariant (\forall int j; 0 <= j && j < i;!secret ==> \dl_array2seq(chosen[j]) == \dl_array2seq(msg2[j]));
	      loop_invariant \fresh(chosen);
	      loop_invariant (\forall int j; 0 <= j && j < i; chosen[j] != null);
	      loop_invariant (\forall int i; 0 <= i && i <= msg1.length; msg1[i].length == msg2[i].length);
	      assignable chosen[*];
	      decreases chosen.length - i;
	     @*/
		for(int i=0; i<chosen.length; ++i){			
			chosen[i] = copyMsg(msg1[i], msg2[i]);		
		}
		return chosen;
	}
	/**
     *If secret is set returns a copy of msg1 otherwise returns a copy of msg2.     
     */
    /*@
      public normal_behaviour
      requires msg1 != null && msg2 != null && msg1.length == msg2.length;      
      ensures secret ==> \dl_array2seq(\result) == \dl_array2seq(msg1);
      ensures !secret ==> \dl_array2seq(\result) == \dl_array2seq(msg2);
      ensures \fresh(\result);
      assignable \nothing;
     @*/
	private static/*@helper@*/ byte[] copyMsg(byte[] msg1, byte[] msg2) {
		byte[] msg = new byte[msg1.length];
		/**
		 * JOANA Change: let secret only decide about the content,
		 * not about pointers, and not about (abnormal) program termination.
		 * rationale:
		 * a) With "msg = secret? msg1[i] : msg2[i]",
		 * the secret value taints the value of the pointer msg. This means
		 * that *every* dereferencing of msg (including msg.length) is also
		 * tainted.
		 * b) With "msg = secret? msg1[i] : msg2[i]", the secret also decides
		 * which of the two array accesses is executed. This means that the
		 * secret value may also decide whether the program crashes or not, since
		 * Joana does not know how long arrays are and assumes that every array
		 * access may fail. Hence, the secret value decides whether every subsequent
		 * program action (in particular: the public outputs) happens or not.
		 * A workaround is to push the decision on the secret value as far as possible
		 * into the innermost loop. This means:
		 * - instead of assigning pointers, a new array is created
		 * - this new array is initialized elementwise in an inner loop
		 * - for each element, both the respective elements of msg1[i] and msg2[i] are read
		 *   (into local variables)
		 * - the secret is only used to decide between the values of these two variables
		 * - the result is written into the new array
		 * This way, the secret value does not decide about which pointer is assigned or which
		 * array access may fail but only which value is selected.
		 */
		/*@
		  loop_invariant 0 <= j && j <= msg.length;
		  loop_invariant msg1 != null && msg2 != null;
		  loop_invariant \fresh(msg);
		  loop_invariant msg1.length == msg2.length && msg.length == msg1.length;
		  loop_invariant (\forall int k; 0 <= k && k < j; (secret ==> (msg[k] == msg1[k])) && (!secret ==> (msg[k] == msg2[k])));
		  assignable msg[*];
		  decreases msg.length - j;
		 @*/		
		for (int j=0; j<msg.length; j++) {
			byte b1 = msg1[j];
			byte b2 = msg2[j];
			byte b = secret?b1:b2;
			msg[j] = b;
		}
		return msg;
	}
}