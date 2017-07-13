package verif.functionalities.pkisig;

import verif.utils.MessageTools;
import verif.lib.crypto.CryptoLib;

public class Verifier {
	protected byte[] verifKey;

	public Verifier(byte[] verifKey) {
		this.verifKey = verifKey;
	}
    /*@ public behaviour
        ensures true;
        assignable verif.environment.Environment.inputCounter, verif.environment.Environment.result;
    @*/
	public /*@helper@*/boolean verify(byte[] signature, byte[] message) {
		return CryptoLib.verify(message, signature, verifKey);
	}

	public byte[] getVerifKey() {
		return MessageTools.copyOf(verifKey);
	}

	protected Verifier copy() {
		return new Verifier(verifKey);
	}
}
