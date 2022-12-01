package de.buw.fm4se.java_smt.pcconfig;

import java.util.Map;
import java.util.HashMap;
import java.util.Scanner;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.IntegerFormulaManager;
import org.sosy_lab.java_smt.api.Model;
import org.sosy_lab.java_smt.api.Model.ValueAssignment;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;
import org.sosy_lab.java_smt.api.ProverEnvironment;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

import scala.beans.BooleanBeanProperty;

public class PcConfigGeneratorAndSolver {

	public static void main(String[] args) throws Exception {
		
		Scanner scan = new Scanner(System.in);
		System.out.print("Please enter a budget: ");
		int budget = scan.nextInt();
		scan.close();
		
		
		
		System.out.print("\nSearching for a configuration costing at most " + budget);
		
		// TODO implement the translation to SMT and the interpretation of the model

		// setting up SMT solver related stuff
		Configuration config = Configuration.fromCmdLineArguments(args);
		LogManager logger = BasicLogManager.create(config);
		ShutdownManager shutdown = ShutdownManager.create();

		// we use PRINCESS SMT solver as SMTINTERPOL did not support integer multiplication
		SolverContext context = SolverContextFactory.createSolverContext(config, logger, shutdown.getNotifier(),
				Solvers.PRINCESS);

		FormulaManager fmgr = context.getFormulaManager();

		IntegerFormulaManager imgr = fmgr.getIntegerFormulaManager();
		BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();

		Map<String, List<HashMap<String, BooleanFormula>>> componentList = new HashMap<>();
		Map<BooleanFormula, Integer> priceList = new HashMap<>();
		String[] componentType = { "CPU", "motherboard", "RAM", "GPU", "storage", "opticalDrive", "cooler" };
		
		for (String type : componentType) {
			Map<String, Integer> components = PcConfigReader.getComponents(type);
			for (String cmp : components.keySet()) {
				BooleanFormula cmpBool = bmgr.makeVariable(cmp);
				HashMap<String, BooleanFormula> cmpMap = new HashMap<>();

				cmpMap.put(cmp, cmpBool);
				priceList.put(cmpBool, components.get(cmp));

				List<HashMap<String, BooleanFormula>> compByType = componentList.get(type);
				if (compByType == null) {
					List<HashMap<String, BooleanFormula>> compByTypeNew = new ArrayList<HashMap<String, BooleanFormula>>();
					compByTypeNew.add(cmpMap);
					componentList.put(type, compByTypeNew);
				}
				else {
					compByType.add(cmpMap);
					componentList.put(type, compByType);
				}
			}
		}
		// System.out.println(componentList);

		/*
		Constraint #1 : Every valid PC needs at least component from each of these categories: CPU, motherboard, RAM, and storage
		Constraint #2 : Read constraints between components from another file.
		Constraint #3 : Return model, if sat. Return message if unsat. 
		*/
		String[] mandatoryComps = { "CPU", "motherboard", "RAM", "storage" };
		List<BooleanFormula> compListAll = new ArrayList<>();
		for (String manComp : mandatoryComps) {
			List<BooleanFormula> compList = new ArrayList<>();
			for (Map<String, BooleanFormula> hMap : componentList.get(manComp)) {
				for (Map.Entry<String, BooleanFormula> entry : hMap.entrySet()) {
					compList.add(entry.getValue());
				}
			}
			compListAll.add(bmgr.or(compList));
		}
		
		BooleanFormula constraint1 = bmgr.and(compListAll);

		String[] constraintType = { "requires", "excludes" };
		List<BooleanFormula> constList = new ArrayList<>();
		for (String kind : constraintType) {
			for (String[] pair : PcConfigReader.getConstraints(kind)) {
				BooleanFormula pair0 = null;
				BooleanFormula pair1 = null;
				for (String compType : componentType) {
					for (Map<String, BooleanFormula> hMap : componentList.get(compType)) {
						for (Map.Entry<String, BooleanFormula> entry : hMap.entrySet()) {
							if (Objects.equals(entry.getKey(), pair[0])) {
								pair0 = entry.getValue();
							}
							if (Objects.equals(entry.getKey(), pair[1])) {
								pair1 = entry.getValue();
							}
						}
					}
				}
				if (Objects.equals(kind, "requires")) {
					constList.add(bmgr.implication(pair0, pair1));
				} else if (Objects.equals(kind, "excludes")) {
					// excludes constraint
					constList.add(bmgr.implication(pair0, bmgr.not(pair1)));
				}
			}
		}
		BooleanFormula constraint2 = bmgr.and(constList);
		// Calculate the price
		List<IntegerFormula> costings = new ArrayList<>();

		for (String compType : componentType) {
			for (Map<String, BooleanFormula> hMap : componentList.get(compType)) {
				for (Map.Entry<String, BooleanFormula> entry : hMap.entrySet()) {
					BooleanFormula comp = entry.getValue();
					costings.add(bmgr.ifThenElse(comp, imgr.makeNumber(priceList.get(comp)), imgr.makeNumber(0)));
				}
			}
		}
		BooleanFormula budgetConstraint = imgr.lessOrEquals(imgr.sum(costings), imgr.makeNumber(budget));

		try (ProverEnvironment prover = context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
			prover.addConstraint(constraint1);
			prover.addConstraint(constraint2);
			prover.addConstraint(budgetConstraint);

			boolean isUnsat = prover.isUnsat();
			if (!isUnsat) {
				Model model = prover.getModel();
				// print whole model
				System.out.println(model);
			} else {
				System.out.println("problem is UNSAT :-(");
			}
		}
		// System.out.println(priceList);
		// System.out.println(componentList);

		// INFO this is just to see how to access the information from the files
		// System.out.println("\nAvailable components:");
		// printComponents("CPU");
		// printComponents("motherboard");
		// printComponents("RAM");
		// printComponents("GPU");
		// printComponents("storage");
		// printComponents("opticalDrive");
		// printComponents("cooler");
		
		// System.out.println("\nConstraints:");
		// printConstraints("requires");
		// printConstraints("excludes");
	}

	private static void printConstraints(String kind) {
		for (String[] pair : PcConfigReader.getConstraints(kind)) {
			System.out.println(pair[0] + " " + kind + " " + pair[1]);
		}		
	}

	private static void printComponents(String type) {
		Map<String, Integer> compoents = PcConfigReader.getComponents(type);
		for (String cmp : compoents.keySet()) {
			System.out.println(cmp + " costs " + compoents.get(cmp));
		}
	}

}
