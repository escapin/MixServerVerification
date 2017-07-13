package verif.functionalities.pkisig;

import verif.lib.crypto.CryptoLib;

public final class UncorruptedVerifier extends Verifier {
	private /*@spec_public@*/Signer.Log log;

	UncorruptedVerifier(byte[] verifKey, Signer.Log log) {
		super(verifKey);
		this.log = log;
	}
    /*@public behaviour
       requires log.messages != null;
       ensures \result ==> \dl_array2seq(log.messages) == \dl_array2seq(message) ;  
       assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result;
    @*/
	public boolean verify(byte[] signature, byte[] message) {
		// verify both that the signature is correc (using the real verification 
		// algorithm) and that the message has been logged as signed
		return CryptoLib.verify(message, signature, verifKey) && log.contains(message);
	}

	protected Verifier copy() {
		return new UncorruptedVerifier(verifKey, log);
	}
}
