package selectvoting.system.core;

public class ConservativeExtension
{
	private static byte[][] messages;
	
	public static void getMessages(byte[][] msg)
	{
		messages=msg;
	}
	
	public static byte[][] retrieveMessages()
	{
		Utils.sort(messages, 0, messages.length);
		return messages;
	}
}
