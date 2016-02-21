package verif.functionalities.pkisig;

import static verif.utils.MessageTools.copyOf;
import verif.lib.crypto.CryptoLib;

public class Verifier {
	protected byte[] verifKey;

	public Verifier(byte[] verifKey) {
		this.verifKey = verifKey;
	}

	public boolean verify(byte[] signature, byte[] message) {
		return CryptoLib.verify(message, signature, verifKey);
	}

	public byte[] getVerifKey() {
		return copyOf(verifKey);
	}

	protected Verifier copy() {
		return new Verifier(verifKey);
	}
}
