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

	private static boolean setEquality(byte[][] arr1, byte[][] arr2) {
		if(arr1.length!=arr2.length) return false;
		byte[][] a1=MessageTools.copyOf(arr1);
		byte[][] a2=MessageTools.copyOf(arr2);
		Utils.sort(a1, 0, a1.length);
		Utils.sort(a2, 0, a2.length);
		for(int i=0;i<a1.length;i++)
			if(!MessageTools.equal(a1[i],a2[i])) 
				return false;
		return true;
	}
	
	// MAIN METHOD:
	
	// one secret bit
	private static boolean secret; // the HIGH value
	
	
	public static void main (String[] a) throws Throwable {

		// SETUP THE COMPONENTS
		
		byte[] electionID = Environment.untrustedInputMessage();
		
		// create the cryptographic functionalities
		Decryptor mixDecr = new Decryptor();
		Encryptor mixEncr = mixDecr.getEncryptor();
		Signer mixSign = new Signer();
		
		Signer precServSign = new Signer();
		Verifier precServVerif = precServSign.getVerifier(); 
		
		NonceGen noncegen = new NonceGen(); // nonce generation functionality
		
		MixServer mixServ = 
				new  MixServer(mixDecr, mixSign, precServVerif, electionID);
		
		
		
		// let the adversary choose how many messages have to 
		// be sent to the mix server
		int numberOfMessages = Environment.untrustedInput();
		
		// let the adversary decide the length of the messages 
		// all the messages must have the same length: 
		int lengthOfTheMessages = Environment.untrustedInput();
		
		
		// let the environment determine the two arrays of messages
		byte[][] msg1 = new byte[numberOfMessages][];
		byte[][] msg2 = new byte[numberOfMessages][];
		for(int i=0; i<numberOfMessages; ++i){
			msg1[i] = Environment.untrustedInputMessage();
			msg2[i] = Environment.untrustedInputMessage();
			// the environment must provide all the messages with the same, prefixed length
			// otherwise, the adversary can distinguish which vector of messages is encrypting.
			if(msg1[i].length!=lengthOfTheMessages || msg2[i].length!=lengthOfTheMessages)
				throw new Throwable();
		}
		
		// the two vectors must be two permutations of the same set
		if(!setEquality(msg1, msg2))
			throw new Throwable();
		
		ConservativeExtension.storeMessages(msg1);
		
		
		// encrypt each message, along with the election ID as expected by the mix server 
		byte[][] encrMsg = new byte[numberOfMessages][];
		for(int i=0; i<numberOfMessages; ++i){
			byte[] msg = secret? msg1[i] : msg2[i];
			encrMsg[i] = mixEncr.encrypt(MessageTools.concatenate(electionID, msg));
		}
			
		
		// FORMAT THE DATA FOR THE MIX SERVER
		
		Utils.sort(encrMsg, 0, encrMsg.length);
		
		byte[] asAMessage=Utils.concatenateMessageArray(encrMsg, encrMsg.length);
		// add election id, tag and sign
		byte[] elID_ballots = MessageTools.concatenate(electionID, asAMessage);
		byte[] input = MessageTools.concatenate(Tag.BALLOTS, elID_ballots);
		byte[] signatureOnInput = precServSign.sign(input);
		byte[] signedInput = MessageTools.concatenate(input, signatureOnInput);
		
		
		// MODEL THE NETWORK
		
		// send the message over the network, controlled by the adversary
		Environment.untrustedOutputMessage(signedInput);
		
		// retrieve the message from the network
		byte[] mixServerInput=Environment.untrustedInputMessage();
		// what I get from the network is supposed to be the the message I sent (signedInput)
		// otherwise, if the message is not on the supposed format the mix server will 
		// throw an exception
		
		
		// let the mix server process the ballots 
		byte[] mixServerOutput=mixServ.processBallots(mixServerInput);
		
		
		// send the output of the mix server over the network
		Environment.untrustedOutputMessage(mixServerOutput);
		
	}
}