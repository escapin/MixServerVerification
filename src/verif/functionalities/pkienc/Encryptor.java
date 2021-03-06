package verif.functionalities.pkienc;

import verif.utils.MessageTools;
import verif.lib.crypto.CryptoLib;


/** Encryptor encapsulating possibly corrupted public key.
 */
public class Encryptor {
	protected /*@spec_public nullable@*/byte[] publicKey;

	/*@
	public normal_behaviour
	ensures this.publicKey == publicKey;
	assignable this.publicKey;
	@*/
	public Encryptor(byte[] publicKey) {
		this.publicKey = publicKey;
	}
	/*@
	public behaviour
	ensures true;
	assignable verif.environment.Environment.result, verif.environment.Environment.inputCounter; 
	@*/
	public byte[]/*@helper@*/ encrypt(byte[] message) {
		return MessageTools.copyOf(CryptoLib.pke_encrypt(MessageTools.copyOf(message), MessageTools.copyOf(publicKey)));
	}

	public byte[] getPublicKey() {
		return MessageTools.copyOf(publicKey);
	}
    
	protected Encryptor copy() {
		return new Encryptor(publicKey);
	}	
}

