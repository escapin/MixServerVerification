package verif.functionalities.pkisig;

import verif.utils.MessageTools;
import verif.lib.crypto.CryptoLib;

public class Verifier {
	protected byte[] verifKey;

	public Verifier(byte[] verifKey) {
		this.verifKey = verifKey;
	}
    /*@ public normal_behaviour
        ensures \result == \dl_mSigOf(\dl_array2seq(signature), \dl_array2seq(message));
        assignable \nothing;
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
