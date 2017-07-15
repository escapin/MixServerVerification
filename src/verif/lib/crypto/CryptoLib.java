package verif.lib.crypto;

import verif.environment.Environment;

public class CryptoLib {
	/*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] nextNonce() {
		// input
		Environment.untrustedOutput(0x100);
		// output
		return Environment.untrustedInputMessage();
	}
	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] symkey_generateKey() {
		// input
		Environment.untrustedOutput(0x91);
		// output
		return Environment.untrustedInputMessage();
	}
	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] symkey_encrypt(/*@nullable@*/byte[] key, /*@nullable@*/byte[] msg) {
		// input
		Environment.untrustedOutput(0x92);
		Environment.untrustedOutputMessage(msg);
		Environment.untrustedOutputMessage(key);
		// output
		return Environment.untrustedInputMessage();
	}
	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] symkey_decrypt(/*@nullable@*/byte[] key, /*@nullable@*/byte[] msg) {
		// input
		Environment.untrustedOutput(0x93);
		Environment.untrustedOutputMessage(msg);
		Environment.untrustedOutputMessage(key);
		// output
		return Environment.untrustedInputMessage();
	}

	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] pke_encrypt(/*@nullable@*/byte[] message, /*@nullable@*/byte[] publKey) {
		// input
		Environment.untrustedOutput(0x66); // Function code for pke_encrypt
		Environment.untrustedOutputMessage(message);
		Environment.untrustedOutputMessage(publKey);
		// output
		return Environment.untrustedInputMessage();
	}
	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] pke_decrypt(/*@nullable@*/byte[] message, /*@nullable@*/byte[] privKey) {
		// input
		Environment.untrustedOutput(0x77); // Function code for pke_decrypt
		Environment.untrustedOutputMessage(message);
		Environment.untrustedOutputMessage(privKey);		
		// output
		return Environment.untrustedInputMessage();
	}
	 /*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/KeyPair pke_generateKeyPair() {
		// input
		Environment.untrustedOutput(0x88); // Function code for pke_generateKeyPair
		
		// output
		KeyPair resval = null;
		if( Environment.untrustedInput()==0 ) {
			resval = new KeyPair();
			resval.privateKey = Environment.untrustedInputMessage();
			resval.publicKey = Environment.untrustedInputMessage();
		}
		return resval;
	}
    /*@ public behaviour
        ensures true;
        assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/boolean verify(/*@nullable@*/byte[] message, /*@nullable@*/byte[] signature,/*@nullable@*/ byte[] pubKey) {
		// input
		Environment.untrustedOutput(0x22); // Function code for digital signature verification ds_verify
		Environment.untrustedOutputMessage(message);
		Environment.untrustedOutputMessage(signature);
		Environment.untrustedOutputMessage(pubKey);		
		// output
		return Environment.untrustedInput() != 0;
	}
	/*@ public behaviour
        ensures true;
        assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] sign(/*@nullable@*/byte[] message, /*@nullable@*/byte[] signingKey) {
		// input
		Environment.untrustedOutput(0x66); // Function code for pke_encrypt
		Environment.untrustedOutputMessage(message);
		Environment.untrustedOutputMessage(signingKey);
		// output
		return Environment.untrustedInputMessage();
	}
	/*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/byte[] virifySignature(/*@nullable@*/byte[] signature, /*@nullable@*/byte[] message,/*@nullable@*/ byte[] verificationKey) {
		// input
		Environment.untrustedOutput(0x66); // Function code for pke_encrypt
		Environment.untrustedOutputMessage(message);
		Environment.untrustedOutputMessage(signature);
		Environment.untrustedOutputMessage(verificationKey);
		// output
		return Environment.untrustedInputMessage();
	}
	/*@ public behaviour
    ensures true;
    assignable Environment.result, Environment.inputCounter;
    @*/
	public static /*@nullable@*/ KeyPair generateSignatureKeyPair() {
		// input
		Environment.untrustedOutput(0x88); // Function code for generateSignatureKeyPair

		// ouptut
		KeyPair resval = null;
		if( Environment.untrustedInput()==0 ) {
			resval = new KeyPair();
			resval.privateKey = Environment.untrustedInputMessage();
			resval.publicKey = Environment.untrustedInputMessage();
		}
		return resval;
	}

}
