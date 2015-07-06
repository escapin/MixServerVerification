package de.unitrier.infsec.functionalities.pkenc;


import de.unitrier.infsec.lib.crypto.CryptoLib;
import de.unitrier.infsec.lib.crypto.KeyPair;
import de.unitrier.infsec.utils.MessageTools;

// THIS FUNCTIONALITY IS OBSOLETE. USE PKI INSTEAD.

/**
 * Ideal functionality for public-key encryption: Decryptor
 */
public final class Decryptor {
	
	private byte[] privKey; 
	private byte[] publKey;
	private EncryptionLog log;

	public Decryptor() {
		KeyPair keypair = CryptoLib.pke_generateKeyPair();
		publKey = MessageTools.copyOf(keypair.publicKey);  
		privKey = MessageTools.copyOf(keypair.privateKey); 
		log = new EncryptionLog();
	}

	
	public byte[] decrypt(byte[] message) {
		byte[] messageCopy = MessageTools.copyOf(message); 
		if (!log.containsCiphertext(messageCopy)) {
			return MessageTools.copyOf( CryptoLib.pke_decrypt(MessageTools.copyOf(privKey), messageCopy) );
		} else {
			return MessageTools.copyOf( log.lookup(messageCopy) );
		}
	}
	
	public Encryptor getEncryptor() {
        return new Encryptor(publKey, log);
    }
	
	///// IMPLEMENTATION //////
	
	static class EncryptionLog {

		private static class MessagePairList {
			byte[] ciphertext;
			byte[] plaintext;
			MessagePairList next;
			public MessagePairList(byte[] ciphertext, byte[] plaintext, MessagePairList next) {
				this.ciphertext = ciphertext;
				this.plaintext = plaintext;
				this.next = next;
			}
		}

		private MessagePairList first = null;

		public void add(byte[] plaintext, byte[] ciphertext) {
			first = new MessagePairList(ciphertext, plaintext, first);
		}

		byte[] lookup(byte[] ciphertext) {
			for( MessagePairList node = first;  node != null;  node = node.next ) {
				if( MessageTools.equal(node.ciphertext, ciphertext) )
					return node.plaintext;
			}
			return null;
		}

		boolean containsCiphertext(byte[] ciphertext) {
			return lookup(ciphertext) != null;
		}
	}
}
