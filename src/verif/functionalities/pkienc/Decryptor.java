package verif.functionalities.pkienc;

import verif.lib.crypto.CryptoLib;
import verif.lib.crypto.KeyPair;
import verif.utils.MessageTools;


/** An object encapsulating the private and public keys of some party. */
public class Decryptor {
	private/*@nullable@*/ byte[] publicKey;
	private/*@nullable@*/ byte[] privateKey;
	private/*@spec_public@*/ EncryptionLog log;
	
    /*@public behaviour
       ensures \fresh(log);
       ensures log.ciphertext.length == 0;
       ensures log.plaintext.length == 0;
       ensures \fresh(this);
    @*/
	public /*@helper@*/Decryptor() {
		KeyPair keypair = CryptoLib.pke_generateKeyPair();
		this.privateKey = MessageTools.copyOf(keypair.privateKey);
		this.publicKey = MessageTools.copyOf(keypair.publicKey);
		this.log = new EncryptionLog();
	}

	/** "Decrypts" a message by, first trying to find in in the log (and returning
	 *   the related plaintext) and, only if this fails, by using real decryption. */
	/*@
	public normal_behaviour
	ensures \dl_array2seq(\result) == \dl_mDecrypt(\dl_array2seq(message));
	ensures \fresh(\result);
	assignable \nothing;
	@*/
	public /*@helper@*/byte[] decrypt(byte[] message) {
		byte[] messageCopy = MessageTools.copyOf(message);
		if (!log.containsCiphertext(messageCopy)) {
			return MessageTools.copyOf( CryptoLib.pke_decrypt(MessageTools.copyOf(privateKey), messageCopy) );
		} else {
			return MessageTools.copyOf( log.lookup(messageCopy) );
		}
	}

	/** Returns a new uncorrupted encryptor object sharing the same public key, ID, and log. */
	/*@
	   public behaviour
	   ensures \fresh(\result);
	@*/
	public /*@helper@*/Encryptor getEncryptor() {
		return new UncorruptedEncryptor(publicKey, log);
	}
	
	///// IMPLEMENTATION //////
	
	static class EncryptionLog {
		
		byte[][] ciphertext;
		byte[][] plaintext;
	    /*@public normal_behaviour
	       ensures \fresh(ciphertext) && \fresh(plaintext);
	       ensures ciphertext.length == 0 && plaintext.length == 0;
	       assignable ciphertext, plaintext;
	    @*/
        public EncryptionLog(){
        	ciphertext = new byte[0][];
        	plaintext = new byte[0][];
        }

        //@
 
        /*@
        public normal_behaviour
        requires ciphertext.length == plaintext.length;
        ensures \dl_array2seq(ciphertext) == \dl_seqConcat(\old(\dl_array2seq(ciphertext)), \dl_seqSingleton(cipher));
        ensures \dl_array2seq(plaintext) == \dl_seqConcat(\old(\dl_array2seq(plaintext)), \dl_seqSingleton(plain));       
        ensures \fresh(ciphertext) && \fresh(plaintext);
        assignable ciphertext, plaintext;
        @*/
        public void add(byte[] plain, byte[] cipher) {
			byte[][] newPlain = newArray(this.plaintext.length+1);
			byte[][] newCipher = newArray(this.ciphertext.length+1);
			int i = 0;
			/*@
			loop_invariant 0 <= i && i <= ciphertext.length;
			loop_invariant (\forall int j; 0 <= j && j < i; newCipher[j] == \old(ciphertext[j]) && newPlain[j] == \old(plaintext[j]));
			assignable newCipher[*], newPlain[*];
			decreases ciphertext.length - i;
			@*/
			for (; i < this.ciphertext.length; i++) {
				newCipher[i] = this.ciphertext[i];
				newPlain[i] = this.plaintext[i];
			}
			newPlain[i] = plain;
			newCipher[i] = cipher;
			this.plaintext = newPlain;
			this.ciphertext = newCipher;
		}
		
		/*@public normal_behaviour
		   requires n >= 0;
		   ensures \result.length == n;
		   ensures \typeof(\result) == \type(byte[][]);
		   ensures \fresh(\result);
		   assignable \nothing;
		@*/
		private /*@nullable@*/ byte[][] newArray(int n){
			return new byte[n][];
		}
		
		
		/*@public normal_behaviour
		requires ciphertext.length == plaintext.length;
        ensures \result == null ==> (\forall int i; 0 <= i && i < ciphertext.length; \dl_array2seq(cipher) != \dl_array2seq(ciphertext[i]));
        ensures \result != null ==> (\exists int i; 0 <= i && i < ciphertext.length; \dl_array2seq(cipher) == \dl_array2seq(ciphertext[i]) && \result == plaintext[i]); 
        assignable \strictly_nothing;
        @*/
		public /*@nullable@*/ byte[] lookup(byte[] cipher) {
			int i = indexOf(cipher);
			if(i == -1){
				return null;
			}
			else{
				return plaintext[i]; 
			}
		}
		/*@public normal_behaviour
           requires ciphertext.length == plaintext.length;
           ensures \result != -1 ==> ( 0 <= \result && result < ciphertext.length && \dl_array2seq(cipher) == \dl_array2seq(ciphertext[\result]));
           ensures \result == -1 ==> (\forall int i; 0 <= i && i < ciphertext.length; \dl_array2seq(cipher) != \dl_array2seq(ciphertext[i]));
           assignable \strictly_nothing;
         @*/
		public int indexOf(byte[] cipher){

			/*@
			loop_invariant 0 <= i && i <= ciphertext.length;
			loop_invariant (\forall int j; 0 <= j && j < i; \dl_array2seq(cipher) != \dl_array2seq(ciphertext[j]));
			assignable \strictly_nothing;
			decreases ciphertext.length - i;
			@*/
			for(int i = 0; i < ciphertext.length; i++){
				if(MessageTools.equal(cipher, ciphertext[i])){
					return i;
				}
			}
			return -1;
			
			
		}
        /*@public normal_behaviour
           requires ciphertext.length == plaintext.length;
           ensures \result <==> (\exists int i; 0 <= i && i < ciphertext.length; \dl_array2seq(cipher) == \dl_array2seq(ciphertext[i]));
           assignable \strictly_nothing; 
        @*/
		boolean containsCiphertext(byte[] cipher) {
			return lookup(cipher) != null;
		}
	}

}
