package static_ifc;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import static_ifc.AccessInfo.Kind;

import com.ibm.wala.ipa.callgraph.pruned.DoNotPrune;
import com.ibm.wala.ipa.cha.ClassHierarchyException;
import com.ibm.wala.types.ClassLoaderReference;
import com.ibm.wala.types.FieldReference;
import com.ibm.wala.util.CancelException;
import com.ibm.wala.util.NullProgressMonitor;
import com.ibm.wala.util.graph.GraphIntegrity.UnsoundGraphException;

import edu.kit.joana.api.IFCAnalysis;
import edu.kit.joana.api.annotations.AnnotationType;
import edu.kit.joana.api.annotations.NodeAnnotationInfo;
import edu.kit.joana.api.lattice.BuiltinLattices;
import edu.kit.joana.api.sdg.SDGConfig;
import edu.kit.joana.api.sdg.SDGInstruction;
import edu.kit.joana.api.sdg.SDGProgram;
import edu.kit.joana.ifc.sdg.core.SecurityNode;
import edu.kit.joana.ifc.sdg.core.violations.IViolation;
import edu.kit.joana.ifc.sdg.graph.SDGSerializer;
import edu.kit.joana.ifc.sdg.util.JavaMethodSignature;
import edu.kit.joana.util.Stubs;
import edu.kit.joana.wala.core.SDGBuilder.ExceptionAnalysis;
import edu.kit.joana.wala.core.SDGBuilder.FieldPropagation;
import edu.kit.joana.wala.core.SDGBuilder.PointsToPrecision;

public class VerifyMixServer {

	private static final String MAIN_CLASS = "Lselectvoting/system/core/Setup;";
	private static final String ENV_CLASS = "Lde/unitrier/infsec/environment/Environment;";

	public static void main(String[] args) throws ClassHierarchyException, IOException, UnsoundGraphException, CancelException {
		if (args.length != 2) {
			throw new RuntimeException("provide classpath and PDG file!");
		}
		String classPath = args[0];
		JavaMethodSignature entryMethod = JavaMethodSignature.mainMethodOfClass(MAIN_CLASS.substring(1, MAIN_CLASS.length()-1));
		SDGConfig config = new SDGConfig(classPath, entryMethod.toBCString(), Stubs.JRE_14);
		config.setPointsToPrecision(PointsToPrecision.N3_CALL_STACK);
		config.setFieldPropagation(FieldPropagation.OBJ_GRAPH_NO_MERGE_AT_ALL);
		config.setPruningPolicy(new DoNotPrune());
		config.setExceptionAnalysis(ExceptionAnalysis.INTERPROC);
		Set<FieldReference> interestingFields = new HashSet<FieldReference>();
		interestingFields.add(FieldReference.findOrCreate(ClassLoaderReference.Application, MAIN_CLASS, "secret", "Z"));
		interestingFields.add(FieldReference.findOrCreate(ClassLoaderReference.Application, ENV_CLASS, "result", "Z"));
		FindStaticFieldAccesses find = new FindStaticFieldAccesses(interestingFields);
		config.setCGConsumer(find);
		final SDGProgram program = SDGProgram.createSDGProgram(config, System.out, new NullProgressMonitor());
		SDGSerializer.toPDGFormat(program.getSDG(), new FileOutputStream(args[1]));
		IFCAnalysis ana = new IFCAnalysis(program);
		// secret sources: every instruction which reads Setup.secret
		// public sinks: every instruction which writes the static field ENV_CLASS.result 
		for (AccessInfo acc : find.getResult()) {
			System.out.println(acc);
			for (SDGInstruction i : program.getInstruction(JavaMethodSignature.fromString(acc.getMethod()), acc.getBcIndex())) {
				if (acc.getKind() == Kind.READ) {
					ana.addSourceAnnotation(i, BuiltinLattices.STD_SECLEVEL_HIGH);
				} else if (acc.getKind() == Kind.WRITE) {
					ana.addSinkAnnotation(i, BuiltinLattices.STD_SECLEVEL_LOW);
				}
			}
		}
		// sanity check
		if (ana.getSources().isEmpty()) {
			throw new RuntimeException("No sources annotated in PDG! Something is deeply wrong!");
		} else if (ana.getSinks().isEmpty()) {
			throw new RuntimeException("No sinks annotated in PDG! Something is deeply wrong!");
		} else {
			int noSourceNodes = 0;
			int noSinkNodes = 0;
			int noAnnNodes = 0;
			for (Map.Entry<SecurityNode, NodeAnnotationInfo> e : ana.getAnnotatedNodes().entrySet()) {
				if (e.getValue().getAnnotation().getType() == AnnotationType.SOURCE) {
					noSourceNodes++;
				} else if (e.getValue().getAnnotation().getType() == AnnotationType.SINK) {
					noSinkNodes++;
				}
				noAnnNodes++;
			}
			System.out.println(String.format("%d nodes in PDG annotated (%d source(s) and %d sink(s))", noAnnNodes, noSourceNodes, noSinkNodes));
		}
		Collection<? extends IViolation<SecurityNode>> result = ana.doIFC();
		System.out.println(String.format("%d violation(s) found.", result.size()));
	}
}
