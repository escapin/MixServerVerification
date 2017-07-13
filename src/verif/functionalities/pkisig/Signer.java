package verif.functionalities.pkisig;

import verif.lib.crypto.CryptoLib;
import verif.lib.crypto.KeyPair;
import verif.utils.MessageTools;

/**
 * An object encapsulating a signing/verification key pair and allowing a user to
 * create a signature. In this implementation, when a message is signed, a real signature
 * is created (by an algorithm provided in lib.crypto) an the pair message/signature
 * is stores in the log.
 */
final public class Signer {
	private byte[] /*@nullable@*/ verifKey;
	private byte[] /*@nullable@*/signKey;
	private Log log;
	 /*@public behaviour
	    ensures this.log != null;
        ensures \fresh(this);
        assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result;
    @*/
	public/*@helper@*/ Signer() {
		KeyPair keypair = CryptoLib.generateSignatureKeyPair();
		this.signKey = MessageTools.copyOf(keypair.privateKey);
		this.verifKey = MessageTools.copyOf(keypair.publicKey);
		this.log = new Log();
	}
	
	/*@ public behaviour
        ensures true;
	    assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result;	  
	@*/
	public /*@helper nullable@*/byte[] getSignature(byte[] message){
		byte[] signature = CryptoLib.sign(MessageTools.copyOf(message), MessageTools.copyOf(signKey));
		// we make sure that the signing has not failed
		if (signature == null) return null;
		// and that the signature is correct
		if( !CryptoLib.verify(MessageTools.copyOf(message), MessageTools.copyOf(signature), MessageTools.copyOf(verifKey)) )
			return null;
		return signature;
	}

	/*@ public behaviour	
	    ensures \result != null ==>	log.messages == message;
	    assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result, log.messages;    
	  @*/
	public/*@helper nullable@*/ byte[]
			sign(byte[] message) {
		byte[] signature = getSignature(message);
		if(signature == null){
			return null;
		}
		log.add(MessageTools.copyOf(message));
		return MessageTools.copyOf(MessageTools.copyOf(signature));
	}
    /*@public behaviour
       ensures \typeof(\result) == \type(verif.functionalities.pkisig.UncorruptedVerifier);
       ensures ((UncorruptedVerifier)\result).log == this.log;
       ensures \fresh(\result);
       assignable \nothing;
    @*/
	public/*@helper@*/ Verifier getVerifier() {
		return new UncorruptedVerifier(verifKey, log);
	}

	///// IMPLEMENTATION /////

	static class Log {

		private /*@spec_public nullable@*/ byte[] messages;
        /*@ public normal_behaviour
            ensures messages != null;
            assignable messages;
        @*/
		public Log(){
			messages = new byte[0];
		}
        /*@public normal_behaviour
           ensures this.messages == message;
           assignable messages;
        @*/
		public void /*@helper@*/add(byte[] message) {
			this.messages = message;
		}
		
		
		
		/*@public normal_behaviour   
           ensures \result ==>  \dl_array2seq(messages) == \dl_array2seq(message);
           assignable \strictly_nothing;
        @*/
		boolean /*@helper@*/ contains(byte[] message) {
            return MessageTools.equal(messages, message);
		}
	}

}
