package verif.functionalities.pkienc;

import verif.utils.MessageTools;
import verif.lib.crypto.CryptoLib;


/** Encryptor encapsulating possibly corrupted public key.
 */
public class Encryptor {
	protected /*@spec_public@*/byte[] publicKey;

	/*@
	public normal_behaviour
	ensures this.publicKey == publicKey;
	assignable this.publicKey;
	@*/
	public Encryptor(byte[] publicKey) {
		this.publicKey = publicKey;
	}
	/*@
	public normal_behaviour
	ensures \dl_array2seq(\result) == \dl_mEncrypt(\dl_array2seq(message));
	ensures \fresh(\result);
	assignable \nothing;
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

