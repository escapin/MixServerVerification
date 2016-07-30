package verif.functionalities.pkienc;

import verif.utils.MessageTools;
import verif.lib.crypto.CryptoLib;


/**
 * Uncorrupted encryptor.
 * The only way to obtain such an encryptor is through a decryptor.
 * This class is not in the public interface of the corresponding real functionality.
 */	
public final class UncorruptedEncryptor extends Encryptor {
	private /*@spec_public@*/ Decryptor.EncryptionLog log;

	/*@
	public normal_behaviour
	ensures this.publicKey == publicKey;
	ensures this.log == log;
	@*/
	UncorruptedEncryptor(byte[] publicKey, Decryptor.EncryptionLog log) {
		super(publicKey);
		this.log = log;
	}

	public byte[] encrypt(byte[] message) {
		byte[] randomCipher = null;
		// keep asking the environment for the ciphertext, until a fresh one is given:
		while( randomCipher==null || log.containsCiphertext(randomCipher) ) {
			randomCipher = MessageTools.copyOf(CryptoLib.pke_encrypt(MessageTools.getZeroMessage(message.length), MessageTools.copyOf(publicKey)));
		}
		log.add(MessageTools.copyOf(message), randomCipher);
		return MessageTools.copyOf(randomCipher);
	}

	protected Encryptor copy() {
		return new UncorruptedEncryptor(publicKey, log);
	}
}	

