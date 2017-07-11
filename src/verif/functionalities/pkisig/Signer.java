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
    ensures \fresh(this);
    @*/
	public/*@helper@*/ Signer() {
		KeyPair keypair = CryptoLib.generateSignatureKeyPair();
		this.signKey = MessageTools.copyOf(keypair.privateKey);
		this.verifKey = MessageTools.copyOf(keypair.publicKey);
		this.log = new Log();
	}
	
	/*@ public behaviour
	    requires message != null;
	    ensures log != null;
	    diverges true;
	    assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result;	  
	@*/
	public byte[] getSignature(byte[] message){
		byte[] signature = CryptoLib.sign(MessageTools.copyOf(message), MessageTools.copyOf(signKey));
		// we make sure that the signing has not failed
		if (signature == null) return null;
		// and that the signature is correct
		if( !CryptoLib.verify(MessageTools.copyOf(message), MessageTools.copyOf(signature), MessageTools.copyOf(verifKey)) )
			return null;
		return signature;
	}

	/*@ public normal_behaviour	    	    
	    ensures \dl_array2seq(\result) == \dl_mSign(\dl_array2seq(message));
	    ensures \fresh(\result);	
	    assignable \nothing;    
	  @*/
	public/*@helper@*/ byte[]
			sign(byte[] message) {
		byte[] signature = getSignature(message);
		if(signature == null){
			return null;
		}
		log.add(MessageTools.copyOf(message));
		return MessageTools.copyOf(MessageTools.copyOf(signature));
	}
    /*@public behaviour
       ensures \fresh(\result);
    @*/
	public/*@helper@*/ Verifier getVerifier() {
		return new UncorruptedVerifier(verifKey, log);
	}

	///// IMPLEMENTATION /////

	static class Log {

		private /*@spec_public@*/ byte[][] messages;
        /*@ public normal_behaviour
            ensures messages != null;
            assignable messages;
        @*/
		public Log(){
			messages = new byte[0][];
		}
        /*@public normal_behaviour
           requires messages != null;
           ensures (\forall int i; 0 <= i && i < messages.length-1; \old(messages[i]) == messages[i]);
           ensures messages.length == \old(messages.length) + 1;
           ensures \dl_array2seq(messages[messages.length-1]) == \dl_array2seq(message);
           assignable messages;
        @*/
		public void /*@helper@*/add(byte[] message) {
			try{
				byte[][] res = new byte[messages.length+1][];
                /*@
                loop_invariant 0 <= i && i <= messages.length;
                loop_invariant res.length == messages.length + 1;
                loop_invariant (\forall int j; 0 <= j && j < i; res[j] == messages[j]);
                decreases messages.length - i;
                assignable res[0..messages.length];
                @*/
				for(int i= 0; i < messages.length; i++){
					res[i] = messages[i];
				}

				res[res.length-1] = MessageTools.copyOf(message);
				messages = res;
			}catch(Throwable t){}
		}
		
		
		
		/*@public normal_behaviour
		   requires messages != null;		   
           ensures \result <==> (\exists int i; 0 <= i && i < messages.length; \dl_array2seq(messages[i]) == \dl_array2seq(message) );
           assignable \strictly_nothing;
        @*/
		boolean /*@helper@*/ contains(byte[] message) {
			/*@
            loop_invariant 0 <= i && i <= messages.length;           
            loop_invariant (\forall int j; 0 <= j && j < i; \dl_array2seq(messages[j]) != \dl_array2seq(message));
            loop_invariant messages != null;
            decreases messages.length - i;
            assignable \strictly_nothing;
            @*/
			for( int i = 0; i < messages.length; i++ ) {
				if( MessageTools.equal(messages[i], message) )
					return true;
			}
			return false;
		}
	}

}
