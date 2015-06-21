package selectvoting.system.core;

import selectvoting.system.core.Utils.MessageSplitIter;
import de.unitrier.infsec.environment.Environment;
import de.unitrier.infsec.functionalities.nonce.NonceGen;
import de.unitrier.infsec.functionalities.pkenc.Encryptor;
import de.unitrier.infsec.functionalities.pkenc.Decryptor;
import de.unitrier.infsec.functionalities.digsig.Signer;
import de.unitrier.infsec.functionalities.digsig.Verifier;
import de.unitrier.infsec.functionalities.nonce.NonceGen;
import de.unitrier.infsec.utils.MessageTools;

public final class NewSetup {

	// PURE SUPPORT METHODS:
	
	private static int[] createChoices(int numberOfVoters, int numberOfCandidates) {
		final int[] choices = new int[numberOfVoters];
		for (int i=0; i<numberOfVoters; ++i) {
			choices[i] = Environment.untrustedInput();
		}
		return choices;
	}
	
	private static int[] computeResult(int[] choices, int numberOfCandidates) {
		int[] res = new int[numberOfCandidates];
		for (int i=0; i<choices.length; i++) 
			++res[choices[i]];
		return res;
	}

	private static boolean equalResult(int[] r1, int[] r2) {
		for (int j= 0; j<r1.length; j++)
			if (r1[j]!=r2[j]) return false;
		return true;
	}
	
	private static byte[] encryptBallot(Encryptor[] enc, byte[] electionID, byte[] innerBallot){
		byte[] ballot = MessageTools.concatenate(electionID, innerBallot);
		byte[] encrBallot=ballot;
		for(int i=0; i<enc.length;++i)
			encrBallot=enc[i].encrypt(encrBallot);
		return encrBallot;
	}

	
	// MAIN METHOD:
	
	// one secret bit
	private static boolean secret; // the HIGH value
	
/**
 * A setup for modeling one honest mixserver peeling out 
 * one layer of encryption.
 */
	public static void main (String[] a) throws Throwable {
		
		// Let the adversary decide how many voters and candidates
		int numberOfCandidates = Environment.untrustedInput();
		int numberOfVoters = Environment.untrustedInput();
		if (numberOfVoters<=0 || numberOfCandidates<=0)
			throw new Throwable();	// abort
		
		// Let the environment determine two vectors of choices
		int[] choices0 = createChoices(numberOfVoters, numberOfCandidates);
		int[] choices1 = createChoices(numberOfVoters, numberOfCandidates);
		
		// Check that those vectors give the same result
		int[] r0 = computeResult(choices0, numberOfCandidates);
		int[] r1 = computeResult(choices1, numberOfCandidates);
		if (!equalResult(r0,r1))
			throw new Throwable();	// abort if the vectors do not yield the same result
		
		// Let the adversary decide how many mix servers we have
		int nMixServers = Environment.untrustedInput();
		
		// Let the adversary decide the only mix server 
		// which he does not control
		int indexHonestMix = Environment.untrustedInput() % nMixServers;
		
		// Create the encryptors for the mix servers
		Encryptor[] encryptors = new Encryptor[nMixServers];
		for(int i=0; i<nMixServers && i!=indexHonestMix; ++i){
			byte[] pub_key = Environment.untrustedInputMessage();
			encryptors[i] = new Encryptor(pub_key);
		}
		// Create the main components of the honest mix server 
		byte[] electionID = Environment.untrustedInputMessage();
		Decryptor decr = new Decryptor();
		encryptors[indexHonestMix]=decr.getEncryptor();
		Signer sign = new Signer();
		Signer precServSign = new Signer();
		Verifier precServVerif = precServSign.getVerifier();
		MixServer mix = new MixServer(decr, sign, precServVerif, electionID);
		
		// Encrypts n-times 
		NonceGen noncegen = new NonceGen();
		
		byte[][] encrBallots = new byte[numberOfVoters][];
		for(int i=0; i<nMixServers; ++i){
			byte[] nonce = noncegen.nextNonce();
			int choice = secret? choices0[i] : choices1[i];
			byte[] vote = MessageTools.intToByteArray(choice);
			byte[] innerBallot = MessageTools.concatenate(nonce, vote);
			encrBallots[i] = encryptBallot(encryptors, electionID, innerBallot);
		}
		
		// format the data for the first mix server
		Utils.sort(encrBallots, 0, encrBallots.length);
		byte[] ballotsAsAMessage=Utils.concatenateMessageArray(encrBallots, encrBallots.length);
		// add election id, tag and sign
		byte[] elID_ballots = MessageTools.concatenate(electionID, ballotsAsAMessage);
		byte[] input = MessageTools.concatenate(Tag.BALLOTS, elID_ballots);
		byte[] signatureOnInput = precServSign.sign(input);
		byte[] signedInput = MessageTools.concatenate(input, signatureOnInput);
		
		
		
		
		
	}
}