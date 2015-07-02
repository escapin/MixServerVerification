package static_ifc;

import static_ifc.FindStaticFieldAccesses.Kind;

import com.ibm.wala.types.FieldReference;

public class AccessInfo {
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