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

	UncorruptedEncryptor(byte[] publicKey, Decryptor.EncryptionLog log) {
		super(publicKey);
		this.log = log;
	}
    /*@ requires log.ciphertext.length == log.plaintext.length;
        ensures (\forall int i; 0 <= i && i < \old(log.ciphertext.length); \dl_array2seq(log.ciphertext[i]) != \dl_array2seq(\result));
        ensures \dl_array2seq(log.ciphertext) == \dl_seqConcat(\old(\dl_array2seq(log.ciphertext)), \dl_seqSingleton(\result));
        ensures \dl_array2seq(log.plaintext) == \dl_seqConcat(\old(\dl_array2seq(log.plaintext)), \dl_seqSingleton(message));
        ensures \dl_array2seq(log.ciphertext[log.ciphertext.length-1]) == \dl_array2seq(\result);
        assignable verif.environment.Environment.result, verif.environment.Environment.inputCounter; 
    @*/
	public byte[]/*@helper@*/ encrypt(byte[] message) {
		byte[] randomCipher = null;
		randomCipher = MessageTools.copyOf(CryptoLib.pke_encrypt(MessageTools.getZeroMessage(message.length), MessageTools.copyOf(publicKey)));
		
		if(randomCipher == null){
			throw new RuntimeException();
		}
		
		if(log.containsCiphertext(randomCipher)){
			throw new RuntimeException();
		}
		
		log.add(message, randomCipher);
		return MessageTools.copyOf(randomCipher);
	}

	protected Encryptor copy() {
		return new UncorruptedEncryptor(publicKey, log);
	}
}	

