package static_ifc;
import java.util.ArrayList;
import java.util.Set;

import static_ifc.AccessInfo.Kind;

import com.ibm.wala.classLoader.IBytecodeMethod;
import com.ibm.wala.ipa.callgraph.CGNode;
import com.ibm.wala.ipa.callgraph.CallGraph;
import com.ibm.wala.ipa.callgraph.propagation.InstanceKey;
import com.ibm.wala.ipa.callgraph.propagation.PointerAnalysis;
import com.ibm.wala.shrikeCT.InvalidClassFileException;
import com.ibm.wala.ssa.IR;
import com.ibm.wala.ssa.SSAGetInstruction;
import com.ibm.wala.ssa.SSAInstruction;
import com.ibm.wala.ssa.SSAPutInstruction;
import com.ibm.wala.types.FieldReference;

import edu.kit.joana.wala.core.CGConsumer;

class AccessInfo {
	public static enum Kind {
		READ, WRITE;
	}
	private final FieldReference field;
	private final String method;
	private final int bcIndex;
	private final Kind kind;
	public AccessInfo(FieldReference field, String method, int bcIndex,
			Kind kind) {
		super();
		this.field = field;
		this.method = method;
		this.bcIndex = bcIndex;
		this.kind = kind;
	}
	public FieldReference getField() {
		return field;
	}
	public String getMethod() {
		return method;
	}
	public int getBcIndex() {
		return bcIndex;
	}
	public Kind getKind() {
		return kind;
	}

	public String toString() {
		return String.format("(%s:%d) %s of %s", method, bcIndex, kind, field);
	}
}

/**
 * Helper class which finds all places in a given program, where a given static field is written.
 */
public class FindStaticFieldAccesses implements CGConsumer {

	private ArrayList<AccessInfo> accesses = new ArrayList<AccessInfo>();

	private final Set<FieldReference> fields;

	public FindStaticFieldAccesses(Set<FieldReference> fields) {
		this.fields = fields;
	}

	@Override
	public void consume(CallGraph cg, PointerAnalysis<? extends InstanceKey> pts) {
		for (CGNode n : cg) {
			if (!(n.getMethod() instanceof IBytecodeMethod) || n.getIR() == null) {
				// skip synthetic methods
				continue;
			} else {
				IR ir = n.getIR();
				IBytecodeMethod bcMethod = (IBytecodeMethod) n.getMethod();
				FindStaticAccessesInMethod visitor = new FindStaticAccessesInMethod(bcMethod);
				ir.visitAllInstructions(visitor);
			}
		}
	}

	public ArrayList<AccessInfo> getResult() {
		return accesses;
	}

	private class FindStaticAccessesInMethod extends SSAInstruction.Visitor {
		private final IBytecodeMethod bcMethod;

		public FindStaticAccessesInMethod(IBytecodeMethod bcMethod) {
			super();
			this.bcMethod = bcMethod;
		}

		@Override
		public void visitPut(SSAPutInstruction put) {
			if (put.isStatic()) {
				if (fields.contains(put.getDeclaredField())) {
					try {
						accesses.add(new AccessInfo(put.getDeclaredField(), bcMethod.getSignature(), bcMethod.getBytecodeIndex(put.iindex), Kind.WRITE));
					} catch (InvalidClassFileException e) {
						e.printStackTrace();
						return;
					}
				}
			}
		}

		@Override
		public void visitGet(SSAGetInstruction get) {
			if (get.isStatic()) {
				if (fields.contains(get.getDeclaredField())) {
					try {
						accesses.add(new AccessInfo(get.getDeclaredField(), bcMethod.getSignature(), bcMethod.getBytecodeIndex(get.iindex), Kind.READ));
					} catch (InvalidClassFileException e) {
						e.printStackTrace();
						return;
					}
				}
			}
		}

	}
}
