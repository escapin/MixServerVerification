package selectvoting.system.core;

import selectvoting.system.core.Utils.MessageSplitIter;
import de.unitrier.infsec.environment.Environment;
import de.unitrier.infsec.functionalities.nonce.NonceGen;
import de.unitrier.infsec.functionalities.pkenc.Encryptor;
import de.unitrier.infsec.functionalities.pkenc.Decryptor;
import de.unitrier.infsec.functionalities.digsig.Signer;
import de.unitrier.infsec.functionalities.digsig.Verifier;
import de.unitrier.infsec.utils.MessageTools;

public final class Setup {

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
	
	private static byte[] encryptBallot(Encryptor enc, byte[] electionID, byte[] innerBallot){
		byte[] ballot = MessageTools.concatenate(electionID, innerBallot);
		byte[] encrBallot=enc.encrypt(ballot);
		return encrBallot;
	}

	
	// MAIN METHOD:
	
	// one secret bit
	private static boolean secret; // the HIGH value
	
	// the correct result
	static int[] correctResult; /** CONSERVATIVE EXTENSION */
	
	public static void main (String[] a) throws Throwable {

		
		// CREATING THE MAIN COMPONENTS OF THE SYSTEM

		byte[] electionID = Environment.untrustedInputMessage();
		
		// Determine the number of candidates and the number of voters:
		int numberOfCandidates = Environment.untrustedInput();
		int numberOfVoters = Environment.untrustedInput();
		if (numberOfVoters<=0 || numberOfCandidates<=0)
			throw new Throwable();	// abort
		

		// CHOICE VECTORS OF CHOICES AND THE CORRECT RESULT  

		// let the environment determine two vectors of choices
		int[] choices0 = createChoices(numberOfVoters, numberOfCandidates);
		int[] choices1 = createChoices(numberOfVoters, numberOfCandidates);
		
		// check that those vectors give the same result
		int[] r0 = computeResult(choices0, numberOfCandidates);
		int[] r1 = computeResult(choices1, numberOfCandidates);
		if (!equalResult(r0,r1))
			throw new Throwable();	// abort if the vectors do not yield the same result
		
		/** CONSERVATIVE EXTENSION */
		correctResult = r1;
		
		// CREATING THE CRYPTOGRAPHIC FUNCTIONALITIES
		
		// for now, only one (honest) mix server
		Decryptor mixDecr = new Decryptor();
		Signer mixSign = new Signer();
		
		Signer precServSign = new Signer(); 
		Verifier precServVerif = precServSign.getVerifier(); 
		// TODO: create a corrupted Verifier with a public key chosen by the adversary
		
		NonceGen noncegen = new NonceGen(); // nonce generation functionality
		
		
		// THE MIX SERVERS(s)
		
		MixServer mixServ = 
				new  MixServer(mixDecr, mixSign, precServVerif, electionID, numberOfVoters);
			// TODO: add mix servers subsumed by the adversary
		
		
		// LET EACH VOTER VOTE
		
		byte[][] encrBallots = new byte[numberOfVoters][];
		for(int i=0; i<numberOfVoters; ++i) {
			byte[] nonce = noncegen.nextNonce();
			int choice = secret? choices0[i] : choices1[i];
			byte[] vote = MessageTools.intToByteArray(choice);
			byte[] innerBallot = MessageTools.concatenate(nonce, vote);
			
			// TODO: encrypt as many time as the number of mix servers
			encrBallots[i] = encryptBallot(mixServ.getEncryptor(), electionID, innerBallot);
		}
			
		
		// FORMAT THE DATA FOR THE MIX SERVER
		
		Utils.sort(encrBallots, 0, encrBallots.length);
		
		byte[] ballotsAsAMessage=Utils.concatenateMessageArray(encrBallots, encrBallots.length);
		// add election id, tag and sign
		byte[] elID_ballots = MessageTools.concatenate(electionID, ballotsAsAMessage);
		byte[] input = MessageTools.concatenate(Tag.BALLOTS, elID_ballots);
		// FIXME: should the tag be also subsumed by the adversary? I don't think so, but...
		byte[] signatureOnInput = precServSign.sign(input);
		byte[] signedInput = MessageTools.concatenate(input, signatureOnInput);
		
		
		// LET THE MIX SERVER(s) DO THE JOB 
		
		byte[] data=mixServ.processBallots(signedInput);
		
		// CHECK WHETHER THE MIX SERVER(s) DID THE JOB CORRECTLY
		byte[] tagged_payload = MessageTools.first(data);
		byte[] signature = MessageTools.second(data);
		if (!mixServ.getVerifier().verify(signature, tagged_payload))
			throw new Throwable();	// abort
		// check the tag
		byte[] tag = MessageTools.first(tagged_payload);
		if (!MessageTools.equal(tag, Tag.BALLOTS))
			throw new Throwable();	// abort
		byte[] payload = MessageTools.second(tagged_payload);
		// check the election id 
		byte[] el_id = MessageTools.first(payload);
		if (!MessageTools.equal(el_id, electionID))
			throw new Throwable();	// abort
				
		// FINALLY WE GET THE FINAL RESULT
		
		byte[] finalResultAsAMessage = MessageTools.second(payload);
		byte[][] finalResult = new byte[numberOfVoters][];
		int[] votesForCandidates = new int[numberOfCandidates];
		
		int numberOfEntries = 0;
		for( MessageSplitIter iter = new MessageSplitIter(finalResultAsAMessage); iter.notEmpty(); iter.next() ) {
			if (numberOfEntries >= numberOfVoters) // too many entries
				throw new Throwable();
			byte[] current = iter.current();
			byte[] elID = MessageTools.first(current);
			if (!MessageTools.equal(elID, electionID)) // wrong election id
				throw new Throwable();
			byte[] nonce_vote = MessageTools.second(current);
			finalResult[numberOfEntries] = MessageTools.second(nonce_vote); // ignore the nonce, take only the vote
			int choice = MessageTools.byteArrayToInt(finalResult[numberOfEntries]);
			votesForCandidates[choice]++;
			numberOfEntries++;
		}
		if(numberOfEntries!=numberOfVoters) // not all votes found
			throw new Throwable();

		
		/** CONSERVATIVE EXTENSION:
		 * 	 PROVE THAT THE FOLLOWING ASSINGMENT IS REDUNDANT
		 */
		votesForCandidates=correctResult;
		
		for(int i=0; i<votesForCandidates.length; ++i)
			Environment.untrustedOutput(votesForCandidates[i]);
	}
}