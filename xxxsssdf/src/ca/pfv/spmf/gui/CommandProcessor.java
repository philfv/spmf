package ca.pfv.spmf.gui;

/*
 * Copyright (c) 2008-2015 Philippe Fournier-Viger
 *
 * This file is part of the SPMF DATA MINING SOFTWARE
 * (http://www.philippe-fournier-viger.com/spmf).
 *
 * SPMF is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, either version 3 of the License, or (at your option) any later
 * version.
 *
 * SPMF is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR
 * A PARTICULAR PURPOSE. See the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * SPMF. If not, see <http://www.gnu.org/licenses/>.
 */
import java.io.File;
import java.io.IOException;
import java.io.UnsupportedEncodingException;
import java.util.Map;

import ca.pfv.spmf.algorithms.associationrules.IGB.AlgoIGB;
import ca.pfv.spmf.algorithms.associationrules.Indirect.AlgoINDIRECT;
import ca.pfv.spmf.algorithms.associationrules.MNRRules.AlgoMNRRules;
import ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.Database;
import ca.pfv.spmf.algorithms.associationrules.closedrules.AlgoClosedRules;
import ca.pfv.spmf.algorithms.associationrules.fhsar.AlgoFHSAR;
import ca.pfv.spmf.algorithms.clustering.hierarchical_clustering.AlgoHierarchicalClustering;
import ca.pfv.spmf.algorithms.clustering.kmeans.AlgoKMeans;
import ca.pfv.spmf.algorithms.frequentpatterns.MSApriori.AlgoMSApriori;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori.AlgoApriori;
import ca.pfv.spmf.algorithms.frequentpatterns.aprioriTID.AlgoAprioriTID;
import ca.pfv.spmf.algorithms.frequentpatterns.aprioriTIDClose.AlgoAprioriTIDClose;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_HT.AlgoAprioriHT;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_close.AlgoAprioriClose;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_inverse.AlgoAprioriInverse;
import ca.pfv.spmf.algorithms.frequentpatterns.apriori_rare.AlgoAprioriRare;
import ca.pfv.spmf.algorithms.frequentpatterns.cfpgrowth.AlgoCFPGrowth;
import ca.pfv.spmf.algorithms.frequentpatterns.charm.AlgoCharmMFI;
import ca.pfv.spmf.algorithms.frequentpatterns.charm.AlgoCharm_Bitset;
import ca.pfv.spmf.algorithms.frequentpatterns.charm.AlgoDCharm_Bitset;
import ca.pfv.spmf.algorithms.frequentpatterns.dci_closed_optimized.AlgoDCI_Closed_Optimized;
import ca.pfv.spmf.algorithms.frequentpatterns.defme.AlgoDefMe;
import ca.pfv.spmf.algorithms.frequentpatterns.eclat.AlgoDEclat;
import ca.pfv.spmf.algorithms.frequentpatterns.eclat.AlgoDEclat_Bitset;
import ca.pfv.spmf.algorithms.frequentpatterns.eclat.AlgoEclat;
import ca.pfv.spmf.algorithms.frequentpatterns.eclat.AlgoEclat_Bitset;
import ca.pfv.spmf.algorithms.frequentpatterns.fin_prepost.FIN;
import ca.pfv.spmf.algorithms.frequentpatterns.fin_prepost.PrePost;
import ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth;
import ca.pfv.spmf.algorithms.frequentpatterns.hmine.AlgoHMine;
import ca.pfv.spmf.algorithms.frequentpatterns.hui_miner.AlgoFHM;
import ca.pfv.spmf.algorithms.frequentpatterns.hui_miner.AlgoHUIMiner;
import ca.pfv.spmf.algorithms.frequentpatterns.lcm.AlgoLCM;
import ca.pfv.spmf.algorithms.frequentpatterns.lcm.Dataset;
import ca.pfv.spmf.algorithms.frequentpatterns.pascal.AlgoPASCAL;
import ca.pfv.spmf.algorithms.frequentpatterns.relim.AlgoRelim;
import ca.pfv.spmf.algorithms.frequentpatterns.two_phase.AlgoTwoPhase;
import ca.pfv.spmf.algorithms.frequentpatterns.uapriori.AlgoUApriori;
import ca.pfv.spmf.algorithms.frequentpatterns.upgrowth_ihup.AlgoIHUP;
import ca.pfv.spmf.algorithms.frequentpatterns.upgrowth_ihup.AlgoUPGrowth;
import ca.pfv.spmf.algorithms.frequentpatterns.vme.AlgoVME;
import ca.pfv.spmf.algorithms.frequentpatterns.zart.AlgoZart;
import ca.pfv.spmf.algorithms.frequentpatterns.zart.TZTableClosed;
import ca.pfv.spmf.algorithms.sequential_rules.cmdeogun.AlgoCMDeogun;
import ca.pfv.spmf.algorithms.sequential_rules.cmrules.AlgoCMRules;
import ca.pfv.spmf.algorithms.sequential_rules.rulegen.AlgoRuleGen;
import ca.pfv.spmf.algorithms.sequential_rules.rulegrowth.AlgoERMiner;
import ca.pfv.spmf.algorithms.sequential_rules.rulegrowth.AlgoRULEGROWTH;
import ca.pfv.spmf.algorithms.sequential_rules.topseqrules_and_tns.AlgoTNS;
import ca.pfv.spmf.algorithms.sequential_rules.topseqrules_and_tns.AlgoTopSeqRules;
import ca.pfv.spmf.algorithms.sequential_rules.trulegrowth.AlgoTRuleGrowth;
import ca.pfv.spmf.algorithms.sequential_rules.trulegrowth_with_strings.AlgoTRuleGrowth_withStrings;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan.AlgoBIDEPlus;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan.AlgoFEAT;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan.AlgoFSGP;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan.AlgoPrefixSpan;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan.AlgoTSP_nonClosed;
import ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan_with_strings.AlgoPrefixSpan_with_Strings;
import ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.AlgoCM_ClaSP;
import ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.AlgoClaSP;
import ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.AlgoCloSpan;
import ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoFournierViger08;
import ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoPrefixSpanMDSPM;
import ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.multidimensionalpatterns.AlgoDim;
import ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.multidimensionalsequentialpatterns.AlgoSeqDim;
import ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.multidimensionalsequentialpatterns.MDSequenceDatabase;
import ca.pfv.spmf.algorithms.sequentialpatterns.goKrimp.AlgoGoKrimp;
import ca.pfv.spmf.algorithms.sequentialpatterns.goKrimp.DataReader;
import ca.pfv.spmf.algorithms.sequentialpatterns.gsp_AGP.AlgoGSP;
import ca.pfv.spmf.algorithms.sequentialpatterns.gsp_AGP.items.creators.AbstractionCreator;
import ca.pfv.spmf.algorithms.sequentialpatterns.gsp_AGP.items.creators.AbstractionCreator_Qualitative;
import ca.pfv.spmf.algorithms.sequentialpatterns.lapin.AlgoLAPIN_LCI;
import ca.pfv.spmf.algorithms.sequentialpatterns.prefixSpan_AGP.AlgoPrefixSpan_AGP;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.AlgoCMSPADE;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.AlgoSPADE;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.candidatePatternsGeneration.CandidateGenerator;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.candidatePatternsGeneration.CandidateGenerator_Qualitative;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.idLists.creators.IdListCreator;
import ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.idLists.creators.IdListCreator_FatBitmap;
import ca.pfv.spmf.algorithms.sequentialpatterns.spam.AlgoCMSPAM;
import ca.pfv.spmf.algorithms.sequentialpatterns.spam.AlgoSPAM;
import ca.pfv.spmf.algorithms.sequentialpatterns.spam.AlgoTKS;
import ca.pfv.spmf.algorithms.sequentialpatterns.spam.AlgoVGEN;
import ca.pfv.spmf.algorithms.sequentialpatterns.spam.AlgoVMSP;
import ca.pfv.spmf.input.sequence_database_list_strings.SequenceDatabase;
import ca.pfv.spmf.input.transaction_database_list_integers.TransactionDatabase;
import ca.pfv.spmf.tools.dataset_converter.Formats;
import ca.pfv.spmf.tools.dataset_converter.SequenceDatabaseConverter;
import ca.pfv.spmf.tools.dataset_converter.TransactionDatabaseConverter;
import ca.pfv.spmf.tools.dataset_generator.AddTimeStampsToSequenceDatabase;
import ca.pfv.spmf.tools.dataset_generator.SequenceDatabaseGenerator;
import ca.pfv.spmf.tools.dataset_generator.TransactionDatabaseGenerator;
import ca.pfv.spmf.tools.dataset_generator.TransactionDatasetUtilityGenerator;
import ca.pfv.spmf.tools.dataset_stats.SequenceStatsGenerator;
import ca.pfv.spmf.tools.dataset_stats.TransactionStatsGenerator;
import ca.pfv.spmf.tools.other_dataset_tools.FixTransactionDatabaseTool;
import ca.pfv.spmf.tools.resultConverter.ResultConverter;

/**
 * This class executes commands from the command line interface or
 * graphical interface to run the algorithms.
 * 
 * @author Philippe Fournier-Viger
 */
public class CommandProcessor {

	/**
	 * This method run an algorithm. It is called from the GUI interface or when
	 * the user run the jar file from the command line.
	 * 
	 * @param algorithmName
	 *            the name of the algorithm
	 * @param inputFile
	 *            the input file for the algorithm
	 * @param outputFile
	 *            the output file for the algorithm
	 * @param parameters
	 *            the parameters of the algorithm
	 * @throws IOException  exception if an error occurs
	 */
	static void runAlgorithm(String algorithmName,
			String inputFile, String outputFile, String[] parameters) throws IOException {
		// System.out.println("C" + algorithmName);

		// **** CHECK IF ARFF AS INPUT FILE *****
		// FIRST WE WILL CHECK IF IT IS AN ARFF FILE...
		// IF YES, WE WILL CONVERT IT TO SPMF FORMAT FIRST,
		// THEN WE WILL RUN THE ALGORITHM, AND FINALLY CONVERT THE RESULT SO
		// THAT IT CAN
		// BE SHOWED TO THE USER.
		// This map is to store the mapping from ItemID to Attribute value for
		// the conversion
		// from ARFF to SPMF.
		Map<Integer, String> mapItemAttributeValue = null;
		// This variable store the path of the original output file
		String originalOutputFile = null;
		// This variable store the path of the original input file
		String originalInputFile = null;
		// If the file is ARFF
		if (inputFile != null
				&& (inputFile.endsWith(".arff") || inputFile.endsWith(".ARFF"))) {
			// Convert it
			TransactionDatabaseConverter converter = new TransactionDatabaseConverter();
			System.out.println("Converting ARFF to SPMF format.");
			// save the file paths selected by the user
			originalOutputFile = outputFile;
			originalInputFile = inputFile;
			// change the ouptut file path to a temporary file
			inputFile = inputFile + ".tmp";
			outputFile = outputFile + ".tmp";
			mapItemAttributeValue = converter.convertARFFandReturnMap(
					originalInputFile, inputFile, Integer.MAX_VALUE);
			System.out.println("Conversion completed.");
		}

		// ****** NEXT WE WILL APPLY THE DESIRED ALGORITHM ******
		// There is a if condition for each algorithm.
		// I will not describe them one by one because it is
		// straightforward.
		if ("PrefixSpan".equals(algorithmName)) {
			ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);
			// sequenceDatabase.print();
			int minsup = (int) Math
					.ceil((getParamAsDouble(parameters[0]) * sequenceDatabase
							.size())); // we use a minimum support of 2
										// sequences.

			AlgoPrefixSpan algo = new AlgoPrefixSpan();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}
			algo.runAlgorithm(sequenceDatabase, outputFile, minsup);
			algo.printStatistics(sequenceDatabase.size());
		} else if ("PrefixSpan_with_strings".equals(algorithmName)) {

			SequenceDatabase sequenceDatabase = new SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);

			// Create an instance of the algorithm with minsup = 50 %
			AlgoPrefixSpan_with_Strings algo = new AlgoPrefixSpan_with_Strings();

			int minsup = (int) Math
					.ceil((getParamAsDouble(parameters[0]) * sequenceDatabase
							.size())); // we use a minimum support of 2
										// sequences.

			// execute the algorithm
			algo.runAlgorithm(sequenceDatabase, outputFile, minsup);
			algo.printStatistics(sequenceDatabase.size());
		} else if ("SeqDim_(PrefixSpan+Apriori)".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			// If the second boolean is true, the algorithm will use
			// CHARM instead of AprioriClose for mining frequent closed
			// itemsets.
			// This options is offered because on some database, AprioriClose
			// does not
			// perform very well. Other algorithms could be added.
			AlgoDim algoDim = new AlgoDim(false, false);

			AlgoSeqDim algoSeqDim = new AlgoSeqDim();

			// Apply algorithm
			AlgoPrefixSpanMDSPM prefixSpan = new AlgoPrefixSpanMDSPM(minsup);
			algoSeqDim.runAlgorithm(contextMDDatabase, prefixSpan, algoDim,
					false, outputFile);

			// Print results
			algoSeqDim.printStatistics(contextMDDatabase.size());
		} else if ("HirateYamana".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.
			double minInterval = getParamAsDouble(parameters[1]);
			double maxInterval = getParamAsDouble(parameters[2]);
			double minWholeInterval = getParamAsDouble(parameters[3]);
			double maxWholeInterval = getParamAsDouble(parameters[4]);

			ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.SequenceDatabase database = new ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.SequenceDatabase();
			database.loadFile(inputFile);

			// Apply algorithm
			AlgoFournierViger08 algo = new AlgoFournierViger08(minsup,
					minInterval, maxInterval, minWholeInterval,
					maxWholeInterval, null, false, false);

			algo.runAlgorithm(database, outputFile);

			algo.printStatistics();
		} else if ("Fournier08-Closed+time".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.
			double minInterval = getParamAsDouble(parameters[1]);
			double maxInterval = getParamAsDouble(parameters[2]);
			double minWholeInterval = getParamAsDouble(parameters[3]);
			double maxWholeInterval = getParamAsDouble(parameters[4]);

			ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.SequenceDatabase database = new ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.SequenceDatabase();
			database.loadFile(inputFile);

			// Apply algorithm
			AlgoFournierViger08 algo = new AlgoFournierViger08(minsup,
					minInterval, maxInterval, minWholeInterval,
					maxWholeInterval, null, true, true);

			algo.runAlgorithm(database, outputFile);
			algo.printStatistics();
		}
		//
		else if ("SeqDim_(PrefixSpan+Apriori)+time".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.
			double minInterval = getParamAsDouble(parameters[1]);
			double maxInterval = getParamAsDouble(parameters[2]);
			double minWholeInterval = getParamAsDouble(parameters[3]);
			double maxWholeInterval = getParamAsDouble(parameters[4]);

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			AlgoDim algoDim = new AlgoDim(false, false); // <-- here

			AlgoSeqDim algoSeqDim2 = new AlgoSeqDim();

			// Apply algorithm
			AlgoFournierViger08 algoPrefixSpanHirateClustering = new AlgoFournierViger08(
					minsup, minInterval, maxInterval, minWholeInterval,
					maxWholeInterval, null, false, false);
			algoSeqDim2.runAlgorithm(contextMDDatabase,
					algoPrefixSpanHirateClustering, algoDim, false, outputFile);

			// Print results
			algoSeqDim2.printStatistics(contextMDDatabase.size());
			// NOTE : IF YOU DON'T WANT TO MINE *CLOSED* MD-SEQUENCES, JUST
			// CHANGE THE FOUR VALUES "true" for
			// "FALSE" in this example.
		} else if ("SeqDim_(BIDE+AprioriClose)+time".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.
			double minInterval = getParamAsDouble(parameters[1]);
			double maxInterval = getParamAsDouble(parameters[2]);
			double minWholeInterval = getParamAsDouble(parameters[3]);
			double maxWholeInterval = getParamAsDouble(parameters[4]);

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			AlgoDim algoDim = new AlgoDim(true, false); // <-- here

			AlgoSeqDim algoSeqDim2 = new AlgoSeqDim();

			// Apply algorithm
			AlgoFournierViger08 algoPrefixSpanHirateClustering = new AlgoFournierViger08(
					minsup, minInterval, maxInterval, minWholeInterval,
					maxWholeInterval, null, true, true);
			algoSeqDim2.runAlgorithm(contextMDDatabase,
					algoPrefixSpanHirateClustering, algoDim, true, outputFile);

			// Print results
			algoSeqDim2.printStatistics(contextMDDatabase.size());
			// NOTE : IF YOU DON'T WANT TO MINE *CLOSED* MD-SEQUENCES, JUST
			// CHANGE THE FOUR VALUES "true" for
			// "FALSE" in this example.
		} else if ("SeqDim_(BIDE+Charm)+time".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.
			double minInterval = getParamAsDouble(parameters[1]);
			double maxInterval = getParamAsDouble(parameters[2]);
			double minWholeInterval = getParamAsDouble(parameters[3]);
			double maxWholeInterval = getParamAsDouble(parameters[4]);

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			AlgoDim algoDim = new AlgoDim(false, true); // <-- here

			AlgoSeqDim algoSeqDim2 = new AlgoSeqDim();

			// Apply algorithm
			AlgoFournierViger08 algoPrefixSpanHirateClustering = new AlgoFournierViger08(
					minsup, minInterval, maxInterval, minWholeInterval,
					maxWholeInterval, null, true, true);
			algoSeqDim2.runAlgorithm(contextMDDatabase,
					algoPrefixSpanHirateClustering, algoDim, true, outputFile);

			// Print results
			algoSeqDim2.printStatistics(contextMDDatabase.size());
			// NOTE : IF YOU DON'T WANT TO MINE *CLOSED* MD-SEQUENCES, JUST
			// CHANGE THE FOUR VALUES "true" for
			// "FALSE" in this example.
		} else if ("SeqDim_(BIDE+AprioriClose)".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			AlgoDim algoDim = new AlgoDim(true, false);

			AlgoSeqDim algoSeqDim = new AlgoSeqDim();

			// Apply algorithm
			ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoBIDEPlus bideplus = new ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoBIDEPlus(
					minsup);
			algoSeqDim.runAlgorithm(contextMDDatabase, bideplus, algoDim, true,
					outputFile);

			// Print results
			algoSeqDim.printStatistics(contextMDDatabase.size());
		} else if ("SeqDim_(BIDE+Charm)".equals(algorithmName)) {

			double minsup = getParamAsDouble(parameters[0]); // we use a minimum
																// support of 2
																// sequences.

			MDSequenceDatabase contextMDDatabase = new MDSequenceDatabase(); //
			contextMDDatabase.loadFile(inputFile);
			// contextMDDatabase.printContext();

			AlgoDim algoDim = new AlgoDim(false, true);

			AlgoSeqDim algoSeqDim = new AlgoSeqDim();

			// Apply algorithm
			ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoBIDEPlus bideplus = new ca.pfv.spmf.algorithms.sequentialpatterns.fournier2008_seqdim.AlgoBIDEPlus(
					minsup);
			algoSeqDim.runAlgorithm(contextMDDatabase, bideplus, algoDim, true,
					outputFile);

			// Print results
			algoSeqDim.printStatistics(contextMDDatabase.size());
		} else if ("SPAM".equals(algorithmName)) {
			AlgoSPAM algo = new AlgoSPAM();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}
			algo.runAlgorithm(inputFile, outputFile,
					getParamAsDouble(parameters[0]));
			algo.printStatistics();
		} else if ("CM-SPAM".equals(algorithmName)) {
			AlgoCMSPAM algo = new AlgoCMSPAM();
			if ("".equals(parameters[1]) == false) {
				algo.setMinimumPatternLength(getParamAsInteger(parameters[1]));
			}
			if ("".equals(parameters[2]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[2]));
			}
			// get the required items if any (optional)
			if (parameters[3] != null && parameters[3].isEmpty() != true) {
				String[] itemsString = parameters[3].split(",");
				int[] requiredItems = new int[itemsString.length];
				for (int i = 0; i < itemsString.length; i++) {
					requiredItems[i] = Integer.parseInt(itemsString[i]);
				}
				algo.setMustAppearItems(requiredItems);
			}
			// execute the algorithm with minsup = 2 sequences (50 %)
			algo.runAlgorithm(inputFile, outputFile,
					getParamAsDouble(parameters[0])); // minsup = 106 k = 1000
														// BMS
			algo.printStatistics();
		} else if ("VMSP".equals(algorithmName)) {
			AlgoVMSP algo = new AlgoVMSP();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}

			// execute the algorithm with minsup = 2 sequences (50 %)
			algo.runAlgorithm(inputFile, outputFile,
					getParamAsDouble(parameters[0])); // minsup = 106 k = 1000
														// BMS
			algo.printStatistics();
		} else if ("FEAT".equals(algorithmName)) {
			AlgoFEAT algo = new AlgoFEAT();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}
			ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);
			int minsup = (int) (getParamAsDouble(parameters[0]) * sequenceDatabase
					.size()); // we use a minimum support of 2 sequences.

			algo.runAlgorithm(sequenceDatabase, outputFile, minsup);
			algo.printStatistics(sequenceDatabase.size());
		} else if ("FSGP".equals(algorithmName)) {
			AlgoFSGP algo = new AlgoFSGP();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}

			ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);
			int minsup = (int) (getParamAsDouble(parameters[0]) * sequenceDatabase
					.size()); // we use a minimum support of 2 sequences.

			algo.runAlgorithm(sequenceDatabase, outputFile, minsup, true); // PERFORM
																			// PRUNING
																			// ACTIVATED
			algo.printStatistics(sequenceDatabase.size());
		} else if ("VGEN".equals(algorithmName)) {
			AlgoVGEN algo = new AlgoVGEN();
			if ("".equals(parameters[1]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[1]));
			}

			// execute the algorithm
			algo.runAlgorithm(inputFile, outputFile,
					getParamAsDouble(parameters[0]));
			algo.printStatistics();
		} else if ("LAPIN".equals(algorithmName)) {
			AlgoLAPIN_LCI algo = new AlgoLAPIN_LCI();
			// execute the algorithm
			algo.runAlgorithm(inputFile, outputFile,
					getParamAsDouble(parameters[0]));
			algo.printStatistics();
		} else if ("GSP".equals(algorithmName)) {
			AbstractionCreator abstractionCreator = AbstractionCreator_Qualitative
					.getInstance();
			double minSupport = getParamAsDouble(parameters[0]);

			AlgoGSP algo = new AlgoGSP(minSupport, 0, Integer.MAX_VALUE, 0,
					abstractionCreator);
			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.gsp_AGP.items.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.gsp_AGP.items.SequenceDatabase(
					abstractionCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("PrefixSpan_AGP".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.prefixSpan_AGP.items.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.prefixSpan_AGP.items.creators.AbstractionCreator_Qualitative
					.getInstance();
			double minSupport = getParamAsDouble(parameters[0]);

			AlgoPrefixSpan_AGP algo = new AlgoPrefixSpan_AGP(minSupport,
					abstractionCreator);
			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.prefixSpan_AGP.items.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.prefixSpan_AGP.items.SequenceDatabase(
					abstractionCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("SPADE".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			IdListCreator idListCreator = IdListCreator_FatBitmap.getInstance();
			CandidateGenerator candidateGenerator = CandidateGenerator_Qualitative
					.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			AlgoSPADE algo = new AlgoSPADE(minSupport, true, abstractionCreator);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, candidateGenerator, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("SPADE_Parallelized".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			IdListCreator idListCreator = IdListCreator_FatBitmap.getInstance();
			CandidateGenerator candidateGenerator = CandidateGenerator_Qualitative
					.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			AlgoSPADE algo = new AlgoSPADE(minSupport, true, abstractionCreator);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithmParallelized(sd, candidateGenerator, true, false,
					outputFile);
			System.out.println(algo.printStatistics());
		} else if ("CM-SPADE".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			IdListCreator idListCreator = IdListCreator_FatBitmap.getInstance();
			CandidateGenerator candidateGenerator = CandidateGenerator_Qualitative
					.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			AlgoCMSPADE algo = new AlgoCMSPADE(minSupport, true,
					abstractionCreator);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, candidateGenerator, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("SPAM_AGP".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			IdListCreator idListCreator = IdListCreator_FatBitmap.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.AlgoSPAM_AGP algo = new ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.AlgoSPAM_AGP(
					minSupport);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.spade_spam_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("SPAM_PostProcessingClosed".equals(algorithmName)) {
			double minSupport = getParamAsDouble(parameters[0]);

			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreator idListCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreatorStandard_Map
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);

			double relativeMinSup = sd.loadFile(inputFile, minSupport);

			AlgoClaSP algo = new AlgoClaSP(relativeMinSup, abstractionCreator,
					true, false);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("ClaSP".equals(algorithmName)) {
			double minSupport = getParamAsDouble(parameters[0]);

			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreator idListCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreatorStandard_Map
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);

			double relativeMinSup = sd.loadFile(inputFile, minSupport);

			AlgoClaSP algo = new AlgoClaSP(relativeMinSup, abstractionCreator,
					true, true);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("CM-ClaSP".equals(algorithmName)) {
			double minSupport = getParamAsDouble(parameters[0]);

			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.creators.AbstractionCreator_Qualitative
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreator idListCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.idlists.creators.IdListCreatorStandard_Map
					.getInstance();
			ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.clasp_AGP.dataStructures.database.SequenceDatabase(
					abstractionCreator, idListCreator);

			double relativeMinSup = sd.loadFile(inputFile, minSupport);

			AlgoCM_ClaSP algo = new AlgoCM_ClaSP(relativeMinSup,
					abstractionCreator, true, true);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("PrefixSpan_PostProcessingClosed".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.creators.AbstractionCreator_Qualitative
					.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			AlgoCloSpan algo = new AlgoCloSpan(minSupport, abstractionCreator,
					true, false);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.SequenceDatabase();
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());
		} else if ("CloSpan".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.creators.AbstractionCreator abstractionCreator = ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.creators.AbstractionCreator_Qualitative
					.getInstance();

			double minSupport = getParamAsDouble(parameters[0]);

			AlgoCloSpan algo = new AlgoCloSpan(minSupport, abstractionCreator,
					true, true);

			/*
			 * if("".equals(parameters[1]) == false){
			 * algo.setMaximumPatternLength(getParamAsInteger(parameters[1])); }
			 */
			ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.SequenceDatabase sd = new ca.pfv.spmf.algorithms.sequentialpatterns.clospan_AGP.items.SequenceDatabase();
			sd.loadFile(inputFile, minSupport);

			algo.runAlgorithm(sd, true, false, outputFile);
			System.out.println(algo.printStatistics());

			// ///////////////////////////////////////////////////////////end
			// adding by Antonio
			// Gomariz//////////////////////////////////////////////////////////

		} else if ("BIDE+".equals(algorithmName)) {
			ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);
			// sequenceDatabase.print();
			int minsup = (int) Math.ceil(getParamAsDouble(parameters[0])
					* sequenceDatabase.size()); // we use a minimum support of 2
												// sequences.

			AlgoBIDEPlus algo = new AlgoBIDEPlus();
			algo.runAlgorithm(sequenceDatabase, outputFile, minsup);
			algo.printStatistics(sequenceDatabase.size());
		} else if ("BIDE+_with_strings".equals(algorithmName)) {
			SequenceDatabase sequenceDatabase = new SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);
			// sequenceDatabase.print();
			int minsup = (int) Math
					.ceil((getParamAsDouble(parameters[0]) * sequenceDatabase
							.size())); // we use a minimum support of 2
										// sequences.

			ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan_with_strings.AlgoBIDEPlus_withStrings algo = new ca.pfv.spmf.algorithms.sequentialpatterns.BIDE_and_prefixspan_with_strings.AlgoBIDEPlus_withStrings();
			algo.runAlgorithm(sequenceDatabase, outputFile, minsup);
			algo.printStatistics(sequenceDatabase.size());
		} else if ("RuleGrowth".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			AlgoRULEGROWTH algo = new AlgoRULEGROWTH();
			if ("".equals(parameters[2]) == false) {
				algo.setMaxAntecedentSize(getParamAsInteger(parameters[2]));
			}
			if ("".equals(parameters[3]) == false) {
				algo.setMaxConsequentSize(getParamAsInteger(parameters[3]));
			}
			algo.runAlgorithm(minsup, minconf, inputFile, outputFile);
			algo.printStats();
		} else if ("ERMiner".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			AlgoERMiner algo = new AlgoERMiner();
			algo.runAlgorithm(minsup, minconf, inputFile, outputFile);
			algo.printStats();
		} else if ("TRuleGrowth".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			int window = getParamAsInteger(parameters[2]);

			AlgoTRuleGrowth algo = new AlgoTRuleGrowth();
			if ("".equals(parameters[3]) == false) {
				algo.setMaxAntecedentSize(getParamAsInteger(parameters[3]));
			}
			if ("".equals(parameters[4]) == false) {
				algo.setMaxConsequentSize(getParamAsInteger(parameters[4]));
			}
			algo.runAlgorithm(minsup, minconf, inputFile, outputFile, window);
			algo.printStats();
		} else if ("TRuleGrowth_with_strings".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			int window = getParamAsInteger(parameters[2]);

			AlgoTRuleGrowth_withStrings algo = new AlgoTRuleGrowth_withStrings();
			algo.runAlgorithm(minsup, minconf, inputFile, outputFile, window);
			algo.printStats();
		} else if ("CMRules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			AlgoCMRules algo = new AlgoCMRules();
			algo.runAlgorithm(inputFile, outputFile, minsup, minconf);
			algo.printStats();
		} else if ("CMDeo".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			AlgoCMDeogun algo = new AlgoCMDeogun();
			algo.runAlgorithm(inputFile, outputFile, minsup, minconf);
			algo.printStats();
		} else if ("RuleGen".equals(algorithmName)) {
			int minsup = getParamAsInteger(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			AlgoRuleGen rulegen = new AlgoRuleGen();
			rulegen.runAlgorithm(minsup, minconf, inputFile, outputFile);
			rulegen.printStats();

		} else if ("TopSeqRules".equals(algorithmName)) {
			int k = getParamAsInteger(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			ca.pfv.spmf.input.sequence_database_array_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_array_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);

			AlgoTopSeqRules algo = new AlgoTopSeqRules();
			algo.runAlgorithm(k, sequenceDatabase, minconf);
			algo.printStats();
			algo.writeResultTofile(outputFile); // to save results to file
		} else if ("TKS".equals(algorithmName)) {
			int k = getParamAsInteger(parameters[0]);

			AlgoTKS algo = new AlgoTKS();
			if ("".equals(parameters[1]) == false) {
				algo.setMinimumPatternLength(getParamAsInteger(parameters[1]));
			}
			if ("".equals(parameters[2]) == false) {
				algo.setMaximumPatternLength(getParamAsInteger(parameters[2]));
			}
			// get the required items if any (optional)
			if (parameters[3] != null && parameters[3].isEmpty() != true) {
				String[] itemsString = parameters[3].split(",");
				int[] requiredItems = new int[itemsString.length];
				for (int i = 0; i < itemsString.length; i++) {
					requiredItems[i] = Integer.parseInt(itemsString[i]);
				}
				algo.setMustAppearItems(requiredItems);
			}
			// execute the algorithm
			algo.runAlgorithm(inputFile, outputFile, k);
			algo.writeResultTofile(outputFile); // to save results to file
			algo.printStatistics();
		} else if ("TSP_nonClosed".equals(algorithmName)) {
			int k = getParamAsInteger(parameters[0]);

			ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase sequenceDatabase = new ca.pfv.spmf.input.sequence_database_list_integers.SequenceDatabase();
			sequenceDatabase.loadFile(inputFile);

			AlgoTSP_nonClosed algo = new AlgoTSP_nonClosed();

			// execute the algorithm
			algo.runAlgorithm(sequenceDatabase, k);
			algo.writeResultTofile(outputFile); // to save results to file
			algo.printStatistics(sequenceDatabase.size());
		} else if ("TopKRules".equals(algorithmName)) {
			Database database = new Database();
			database.loadFile(inputFile);

			int k = getParamAsInteger(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.AlgoTopKRules algo = new ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.AlgoTopKRules();
			algo.runAlgorithm(k, minconf, database);
			algo.printStats();
			algo.writeResultTofile(outputFile); // to save results to file
		} else if ("TNR".equals(algorithmName)) {
			ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.Database database = new ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.Database();
			database.loadFile(inputFile);

			int k = getParamAsInteger(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			int delta = getParamAsInteger(parameters[2]);

			ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.AlgoTNR algo = new ca.pfv.spmf.algorithms.associationrules.TopKRules_and_TNR.AlgoTNR();
			algo.runAlgorithm(k, minconf, database, delta);
			algo.printStats();
			algo.writeResultTofile(outputFile); // to save results to file
		} else if ("TNS".equals(algorithmName)) {
			// Load database into memory
			ca.pfv.spmf.input.sequence_database_array_integers.SequenceDatabase database = new ca.pfv.spmf.input.sequence_database_array_integers.SequenceDatabase();
			database.loadFile(inputFile);

			int k = getParamAsInteger(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			int delta = getParamAsInteger(parameters[2]);

			AlgoTNS algo = new AlgoTNS();
			algo.runAlgorithm(k, database, minconf, delta);
			algo.printStats();
			algo.writeResultTofile(outputFile); // to save results to file

		} else if ("FPGrowth_itemsets".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			AlgoFPGrowth algo = new AlgoFPGrowth();
			algo.runAlgorithm(inputFile, outputFile, minsup);
			algo.printStats();
		} else if ("FPGrowth_itemsets_with_strings".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth_with_strings.AlgoFPGrowth_Strings algo = new ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth_with_strings.AlgoFPGrowth_Strings();
			algo.runAlgorithm(inputFile, outputFile, minsup);
			algo.printStats();
		} else if ("Apriori_association_rules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			AlgoApriori apriori = new AlgoApriori();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = apriori
					.runAlgorithm(minsup, inputFile, null);
			apriori.printStats();
			int databaseSize = apriori.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf);
			algoAgrawal.printStats();
		} // Sporadic_association_rules
		else if ("Sporadic_association_rules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double maxsup = getParamAsDouble(parameters[1]);
			double minconf = getParamAsDouble(parameters[2]);

			AlgoAprioriInverse apriori = new AlgoAprioriInverse();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = apriori
					.runAlgorithm(minsup, maxsup, inputFile, null);
			apriori.printStats();
			int databaseSize = apriori.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf);
			algoAgrawal.printStats();
		} else if ("Closed_association_rules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			// Loading the transaction database
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
			// database.printDatabase();

			// STEP 1: Applying the Charm algorithm to find frequent closed
			// itemsets
			AlgoCharm_Bitset algo = new AlgoCharm_Bitset();
			ca.pfv.spmf.patterns.itemset_array_integers_with_tids_bitset.Itemsets patterns = algo
					.runAlgorithm(null, database, minsup, true, 10000);
			algo.printStats();

			// STEP 2: Generate all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			AlgoClosedRules algoAgrawal = new AlgoClosedRules();
			algoAgrawal.runAlgorithm(patterns, outputFile, database.size(),
					minconf);
			algoAgrawal.printStats();
		} // IGB
		else if ("IGB".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (Exception e) {
				e.printStackTrace();
			}

			// Applying the Zart algorithm
			AlgoZart zart = new AlgoZart();
			TZTableClosed results = zart.runAlgorithm(database, minsup);
			zart.printStatistics();
			// Generate IGB association rules
			AlgoIGB algoIGB = new AlgoIGB();
			algoIGB.runAlgorithm(results, database.getTransactions().size(),
					minconf, outputFile);
			algoIGB.printStatistics();
		} // Indirect_association_rules
		else if ("Indirect_association_rules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double ts = getParamAsDouble(parameters[1]);
			double minconf = getParamAsDouble(parameters[2]);

			AlgoINDIRECT indirect = new AlgoINDIRECT();
			indirect.runAlgorithm(inputFile, outputFile, minsup, ts, minconf);
			indirect.printStats();
		}// MNR
		else if ("MNR".equals(algorithmName)) {

			System.out
					.println("STEP 1: APPLY ZART TO FIND CLOSED ITEMSETS AND GENERATORS");
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (Exception e) {
				e.printStackTrace();
			}

			// Applying the Zart algorithm
			AlgoZart zart = new AlgoZart();
			TZTableClosed results = zart.runAlgorithm(database, minsup);
			zart.printStatistics();

			System.out.println("STEP 2 : CALCULATING MNR ASSOCIATION RULES");
			// Run the algorithm to generate MNR rules
			AlgoMNRRules algoMNR = new AlgoMNRRules();
			algoMNR.runAlgorithm(outputFile, minconf, results, database.size());
			algoMNR.printStatistics();
		} else if ("FPGrowth_association_rules".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);

			ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth fpgrowth = new ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = fpgrowth
					.runAlgorithm(inputFile, null, minsup);
			fpgrowth.printStats();
			int databaseSize = fpgrowth.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf);
			algoAgrawal.printStats();
		} else if ("FPGrowth_association_rules_with_lift".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			double minlift = getParamAsDouble(parameters[2]);

			ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth fpgrowth = new ca.pfv.spmf.algorithms.frequentpatterns.fpgrowth.AlgoFPGrowth();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = fpgrowth
					.runAlgorithm(inputFile, null, minsup);
			fpgrowth.printStats();
			int databaseSize = fpgrowth.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf, minlift);
			algoAgrawal.printStats();
		} else if ("CFPGrowth++_association_rules".equals(algorithmName)) {
			String misFile = parameters[0];
			double minconf = getParamAsDouble(parameters[1]);

			File file = new File(inputFile);
			String misFileFullPath;
			if (file.getParent() == null) {
				misFileFullPath = misFile;
			} else {
				misFileFullPath = file.getParent() + File.separator + misFile;
			}

			AlgoCFPGrowth cfpgrowth = new AlgoCFPGrowth();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = cfpgrowth
					.runAlgorithm(inputFile, null, misFileFullPath);
			cfpgrowth.printStats();
			int databaseSize = cfpgrowth.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf);
			algoAgrawal.printStats();
		} else if ("CFPGrowth++_association_rules_with_lift"
				.equals(algorithmName)) {
			String misFile = parameters[0];
			double minconf = getParamAsDouble(parameters[1]);
			double minlift = getParamAsDouble(parameters[2]);

			File file = new File(inputFile);
			String misFileFullPath;
			if (file.getParent() == null) {
				misFileFullPath = misFile;
			} else {
				misFileFullPath = file.getParent() + File.separator + misFile;
			}

			AlgoCFPGrowth cfpgrowth = new AlgoCFPGrowth();
			ca.pfv.spmf.patterns.itemset_array_integers_with_count.Itemsets patterns = cfpgrowth
					.runAlgorithm(inputFile, null, misFileFullPath);
			cfpgrowth.printStats();
			int databaseSize = cfpgrowth.getDatabaseSize();

			// STEP 2: Generating all rules from the set of frequent itemsets
			// (based on Agrawal & Srikant, 94)
			ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94 algoAgrawal = new ca.pfv.spmf.algorithms.associationrules.agrawal94_association_rules.AlgoAgrawalFaster94();
			algoAgrawal.runAlgorithm(patterns, outputFile, databaseSize,
					minconf, minlift);
			algoAgrawal.printStats();
		}

		// else if ("CFPGrowth".equals(algorithmName)) {

		//
		// // Applying the algorithm
		// AlgoCFPGrowth algo = new AlgoCFPGrowth();
		// algo.runAlgorithm(inputFile, outputFile, misFileFullPath);
		// algo.printStats();

		else if ("Apriori_TID_bitset".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			AlgoAprioriTID apriori = new AlgoAprioriTID();
			apriori.runAlgorithm(inputFile, outputFile, minsup);
			apriori.printStats();
		} else if ("Apriori".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Applying the Apriori algorithm, optimized version
			ca.pfv.spmf.algorithms.frequentpatterns.apriori.AlgoApriori apriori = new ca.pfv.spmf.algorithms.frequentpatterns.apriori.AlgoApriori();
			apriori.runAlgorithm(minsup, inputFile, outputFile);
			apriori.printStats();
		} else if ("Apriori_with_hash_tree".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			int branch_count = getParamAsInteger(parameters[1]);

			// Applying the Apriori algorithm, optimized version
			AlgoAprioriHT apriori = new AlgoAprioriHT();
			apriori.runAlgorithm(minsup, inputFile, outputFile, branch_count);
			apriori.printStats();
		} else if ("AprioriClose".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			AlgoAprioriClose apriori = new AlgoAprioriClose();
			apriori.runAlgorithm(minsup, inputFile, outputFile);
			apriori.printStats();
		} else if ("Apriori_TID".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			AlgoAprioriTID apriori = new AlgoAprioriTID();
			apriori.runAlgorithm(inputFile, outputFile, minsup);
			apriori.printStats();
		} else if ("Apriori_TIDClose".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			TransactionDatabase database = new TransactionDatabase();
			database.loadFile(inputFile);
			AlgoAprioriTIDClose apriori = new AlgoAprioriTIDClose();
			apriori.runAlgorithm(database, minsup, outputFile);
			apriori.printStats();
		} else if ("AprioriRare".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			AlgoAprioriRare apriori2 = new AlgoAprioriRare();
			// apply the algorithm
			apriori2.runAlgorithm(minsup, inputFile, outputFile);
			apriori2.printStats();
		} else if ("AprioriInverse".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double maxsup = getParamAsDouble(parameters[1]);

			AlgoAprioriInverse apriori = new AlgoAprioriInverse();
			apriori.runAlgorithm(minsup, maxsup, inputFile, outputFile);
			apriori.printStats();
		} else if ("MSApriori".equals(algorithmName)) {
			double beta = getParamAsDouble(parameters[0]);
			double ls = getParamAsDouble(parameters[1]);

			// Applying the MSApriori algorithm
			AlgoMSApriori apriori = new AlgoMSApriori();
			apriori.runAlgorithm(inputFile, outputFile, beta, ls);
			apriori.printStats();
		} else if ("CFPGrowth++".equals(algorithmName)) {
			String misFile = parameters[0];

			File file = new File(inputFile);
			String misFileFullPath;
			if (file.getParent() == null) {
				misFileFullPath = misFile;
			} else {
				misFileFullPath = file.getParent() + File.separator + misFile;
			}

			// Applying the algorithm
			AlgoCFPGrowth algo = new AlgoCFPGrowth();
			algo.runAlgorithm(inputFile, outputFile, misFileFullPath);
			algo.printStats();
		} else if ("FHSAR".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			double minconf = getParamAsDouble(parameters[1]);
			// file for sensitive
			String sarFile = parameters[2];

			File file = new File(inputFile);
			String sarFileFullPath;
			if (file.getParent() == null) {
				sarFileFullPath = sarFile;
			} else {
				sarFileFullPath = file.getParent() + File.separator + sarFile;
			}

			// STEP 1: Applying the FHSAR algorithm to hide association rules
			AlgoFHSAR algorithm = new AlgoFHSAR();
			algorithm.runAlgorithm(inputFile, sarFileFullPath, outputFile,
					minsup, minconf);
			algorithm.printStats();
		} else if ("GoKrimp".equals(algorithmName)) {
			// file for sensitive
			String labelFilePath = parameters[0];
			if (labelFilePath == null) {
				labelFilePath = "";
			} else {
				File file = new File(inputFile);
				if (file.getParent() == null) {
					labelFilePath = parameters[0];
				} else {
					labelFilePath = file.getParent() + File.separator
							+ parameters[0];
				}
			}

			DataReader d = new DataReader();
			AlgoGoKrimp g = d.readData_SPMF(inputFile, labelFilePath);
			g.setOutputFilePath(outputFile); // if not set, then result will be
												// printed to console
			g.gokrimp();
		} else if ("VME".equals(algorithmName)) {
			double threshold = getParamAsDouble(parameters[0]);

			// Applying the algorithm
			AlgoVME algo = new AlgoVME();
			algo.runAlgorithm(inputFile, outputFile, threshold);
			algo.printStats();
		} else if ("KMeans".equals(algorithmName)) {
			int k = getParamAsInteger(parameters[0]);
			// Apply the algorithm
			AlgoKMeans algoKMeans = new AlgoKMeans();
			algoKMeans.runAlgorithm(inputFile, k);
			algoKMeans.printStatistics();
			algoKMeans.saveToFile(outputFile);
		} else if ("Hierarchical_clustering".equals(algorithmName)) {
			int maxDistance = getParamAsInteger(parameters[0]);

			// Apply the algorithm
			AlgoHierarchicalClustering algo = new AlgoHierarchicalClustering();
			algo.runAlgorithm(inputFile, maxDistance);
			algo.printStatistics();
			algo.saveToFile(outputFile);
		} else if ("UApriori".equals(algorithmName)) {
			double expectedsup = getParamAsDouble(parameters[0]);

			ca.pfv.spmf.algorithms.frequentpatterns.uapriori.UncertainTransactionDatabase context = new ca.pfv.spmf.algorithms.frequentpatterns.uapriori.UncertainTransactionDatabase();
			context.loadFile(inputFile);
			AlgoUApriori apriori = new AlgoUApriori(context);
			apriori.runAlgorithm(expectedsup, outputFile);
			apriori.printStats();
		} else if ("HMine".equals(algorithmName)) {
			int minsup = getParamAsInteger(parameters[0]);
			AlgoHMine algorithm = new AlgoHMine();
			algorithm.runAlgorithm(inputFile, outputFile, minsup);
			algorithm.printStatistics();
		} else if ("DCI_Closed".equals(algorithmName)) {
			int minsup = getParamAsInteger(parameters[0]);
			AlgoDCI_Closed_Optimized algorithm = new AlgoDCI_Closed_Optimized();
			algorithm.runAlgorithm(inputFile, outputFile, minsup);
		} else if ("DefMe".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			AlgoDefMe algorithm = new AlgoDefMe();
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
			algorithm.runAlgorithm(outputFile, database, minsup);
			algorithm.printStats();
		} else if ("Charm_bitset".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			AlgoCharm_Bitset algo = new AlgoCharm_Bitset();

			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
			algo.runAlgorithm(outputFile, database, minsup, true, 10000);
			algo.printStats();
		} else if ("dCharm_bitset".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			AlgoDCharm_Bitset algo = new AlgoDCharm_Bitset();

			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
			algo.runAlgorithm(outputFile, database, minsup, true, 10000);
			algo.printStats();
		} else if ("Charm_MFI".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Loading the binary context
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (UnsupportedEncodingException e) {
				e.printStackTrace();
			} catch (IOException e) {
				e.printStackTrace();
			}
			// database.printDatabase();

			// Applying the Charm algorithm
			AlgoCharm_Bitset charm = new AlgoCharm_Bitset();
			charm.runAlgorithm(null, database, minsup, false, 10000);

			// Run CHARM MFI
			AlgoCharmMFI charmMFI = new AlgoCharmMFI();
			charmMFI.runAlgorithm(outputFile, charm.getClosedItemsets());
			charmMFI.printStats(database.size());
		} else if ("Eclat".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Loading the transaction database
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (IOException e) {
				e.printStackTrace();
			}

			AlgoEclat algo = new AlgoEclat();
			algo.runAlgorithm(outputFile, database, minsup, true);
			algo.printStats();
		} else if ("dEclat".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Loading the transaction database
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (IOException e) {
				e.printStackTrace();
			}

			AlgoDEclat algo = new AlgoDEclat();
			algo.runAlgorithm(outputFile, database, minsup, true);
			algo.printStats();
		} else if ("PrePost".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			PrePost prepost = new PrePost();
			prepost.runAlgorithm(inputFile, minsup, outputFile);
			prepost.printStats();
		} else if ("FIN".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			FIN algo = new FIN();
			algo.runAlgorithm(inputFile, minsup, outputFile);
			algo.printStats();
		} else if ("Relim".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Applying the RELIM algorithm
			AlgoRelim algo = new AlgoRelim();
			algo.runAlgorithm(minsup, inputFile, outputFile);
			algo.printStatistics();
		} else if ("Eclat_bitset".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Loading the transaction database
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (IOException e) {
				e.printStackTrace();
			}

			AlgoEclat_Bitset algo = new AlgoEclat_Bitset();
			algo.runAlgorithm(outputFile, database, minsup, true);
			algo.printStats();
		} else if ("dEclat_bitset".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Loading the transaction database
			TransactionDatabase database = new TransactionDatabase();
			try {
				database.loadFile(inputFile);
			} catch (IOException e) {
				e.printStackTrace();
			}

			AlgoDEclat_Bitset algo = new AlgoDEclat_Bitset();
			algo.runAlgorithm(outputFile, database, minsup, true);
			algo.printStats();
		} else if ("Two-Phase".equals(algorithmName)) {
			int minutil = getParamAsInteger(parameters[0]);
			ca.pfv.spmf.algorithms.frequentpatterns.two_phase.UtilityTransactionDatabaseTP database = new ca.pfv.spmf.algorithms.frequentpatterns.two_phase.UtilityTransactionDatabaseTP();
			database.loadFile(inputFile);

			// Applying the Two-Phase algorithm
			AlgoTwoPhase twoPhase = new AlgoTwoPhase();
			ca.pfv.spmf.algorithms.frequentpatterns.two_phase.ItemsetsTP highUtilityItemsets = twoPhase
					.runAlgorithm(database, minutil);

			highUtilityItemsets.saveResultsToFile(outputFile, database
					.getTransactions().size());

			twoPhase.printStats();

		} else if ("HUI-Miner".equals(algorithmName)) {
			int minutil = getParamAsInteger(parameters[0]);
			// Applying the algorithm
			AlgoHUIMiner algo = new AlgoHUIMiner();
			algo.runAlgorithm(inputFile, outputFile, minutil);
			algo.printStats();
		} else if ("FHM".equals(algorithmName)) {
			int minutil = getParamAsInteger(parameters[0]);
			// Applying the algorithm
			AlgoFHM algo = new AlgoFHM();
			algo.runAlgorithm(inputFile, outputFile, minutil);
			algo.printStats();
		} else if ("UPGrowth".equals(algorithmName)) {
			int minutil = getParamAsInteger(parameters[0]);
			// Applying the algorithm
			AlgoUPGrowth algo = new AlgoUPGrowth();
			algo.runAlgorithm(inputFile, outputFile, minutil);
			algo.printStats();
		} else if ("IHUP".equals(algorithmName)) {
			int minutil = getParamAsInteger(parameters[0]);
			// Applying the algorithm
			AlgoIHUP algo = new AlgoIHUP();
			algo.runAlgorithm(inputFile, outputFile, minutil);
			algo.printStats();
		} else if ("Zart".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Load a binary context
			TransactionDatabase context = new TransactionDatabase();
			context.loadFile(inputFile);

			// Apply the Zart algorithm
			AlgoZart zart = new AlgoZart();
			zart.runAlgorithm(context, minsup);
			zart.printStatistics();
			zart.saveResultsToFile(outputFile);
		} else if ("Pascal".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);

			// Applying the Apriori algorithm, optimized version
			AlgoPASCAL algo = new AlgoPASCAL();
			algo.runAlgorithm(minsup, inputFile, outputFile);
			algo.printStats();
		} else if ("LCM".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			Dataset dataset = new Dataset(inputFile);
			AlgoLCM algo = new AlgoLCM();
			algo.runAlgorithm(minsup, dataset, outputFile, false, false);
			algo.printStats();
		} else if ("LCMFreq".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			Dataset dataset = new Dataset(inputFile);
			AlgoLCM algo = new AlgoLCM();
			algo.runAlgorithm(minsup, dataset, outputFile, true, false);
			algo.printStats();
		} else if ("LCMMax".equals(algorithmName)) {
			double minsup = getParamAsDouble(parameters[0]);
			Dataset dataset = new Dataset(inputFile);
			AlgoLCM algo = new AlgoLCM();
			algo.runAlgorithm(minsup, dataset, outputFile, false, true);
			algo.printStats();
		} else if ("Convert_a_sequence_database_to_SPMF_format"
				.equals(algorithmName)) {
			String format = getParamAsString(parameters[0]);
			int seqCount = getParamAsInteger(parameters[1]);

			long startTime = System.currentTimeMillis();
			SequenceDatabaseConverter converter = new SequenceDatabaseConverter();
			converter.convert(inputFile, outputFile, Formats.valueOf(format),
					seqCount);
			long endTIme = System.currentTimeMillis();
			System.out
					.println("Sequence database converted.  Time spent for conversion = "
							+ (endTIme - startTime) + " ms.");
		} else if ("Convert_a_transaction_database_to_SPMF_format"
				.equals(algorithmName)) {
			String format = getParamAsString(parameters[0]);
			int transactionCount = getParamAsInteger(parameters[1]);

			long startTime = System.currentTimeMillis();
			TransactionDatabaseConverter converter = new TransactionDatabaseConverter();
			converter.convert(inputFile, outputFile, Formats.valueOf(format),
					transactionCount);
			long endTIme = System.currentTimeMillis();
			System.out
					.println("Transaction database converted.  Time spent for conversion = "
							+ (endTIme - startTime) + " ms.");
		} else if ("Convert_sequence_database_to_transaction_database"
				.equals(algorithmName)) {
			int transactionCount = getParamAsInteger(parameters[0]);

			long startTime = System.currentTimeMillis();
			TransactionDatabaseConverter converter = new TransactionDatabaseConverter();
			converter.convert(inputFile, outputFile, Formats.SPMF_SEQUENCE_DB,
					transactionCount);
			long endTIme = System.currentTimeMillis();
			System.out
					.println("Sequence database converted.  Time spent for conversion = "
							+ (endTIme - startTime) + " ms.");
		} else if ("Convert_transaction_database_to_sequence_database"
				.equals(algorithmName)) {
			int sequenceCount = getParamAsInteger(parameters[0]);

			long startTime = System.currentTimeMillis();
			SequenceDatabaseConverter converter = new SequenceDatabaseConverter();
			converter.convert(inputFile, outputFile,
					Formats.SPMF_TRANSACTION_DB, sequenceCount);
			long endTIme = System.currentTimeMillis();
			System.out
					.println("Transaction database converted.  Time spent for conversion = "
							+ (endTIme - startTime) + " ms.");
		} else if ("Generate_a_sequence_database".equals(algorithmName)) {
			int p1 = getParamAsInteger(parameters[0]);
			int p2 = getParamAsInteger(parameters[1]);
			int p3 = getParamAsInteger(parameters[2]);
			int p4 = getParamAsInteger(parameters[3]);

			SequenceDatabaseGenerator generator = new SequenceDatabaseGenerator();
			generator.generateDatabase(p1, p2, p3, p4, outputFile, false);
			System.out.println("Sequence database generated.  ");
		} else if ("Add_consecutive_timestamps_to_sequence_database"
				.equals(algorithmName)) {
			AddTimeStampsToSequenceDatabase converter = new AddTimeStampsToSequenceDatabase();
			converter.convert(inputFile, outputFile);
			System.out
					.println("Sequence database with timestamps has been saved.  ");
		} else if ("Generate_a_sequence_database_with_timestamps"
				.equals(algorithmName)) {
			int p1 = getParamAsInteger(parameters[0]);
			int p2 = getParamAsInteger(parameters[1]);
			int p3 = getParamAsInteger(parameters[2]);
			int p4 = getParamAsInteger(parameters[3]);

			SequenceDatabaseGenerator generator = new SequenceDatabaseGenerator();
			generator.generateDatabase(p1, p2, p3, p4, outputFile, true);
			System.out.println("Sequence database generated.  ");
		} else if ("Generate_a_transaction_database".equals(algorithmName)) {
			int p1 = getParamAsInteger(parameters[0]);
			int p2 = getParamAsInteger(parameters[1]);
			int p3 = getParamAsInteger(parameters[2]);

			TransactionDatabaseGenerator generator = new TransactionDatabaseGenerator();
			generator.generateDatabase(p1, p2, p3, outputFile);
			System.out.println("Transaction database generated.  ");
		} else if ("Fix_a_transaction_database".equals(algorithmName)) {
			FixTransactionDatabaseTool tool = new FixTransactionDatabaseTool();
			tool.convert(inputFile, outputFile);
			System.out.println("Finished fixing the transaction database.");
		} else if ("Generate_utility_values_for_transaction_database"
				.equals(algorithmName)) {
			int p1 = getParamAsInteger(parameters[0]);
			int p2 = getParamAsInteger(parameters[1]);

			TransactionDatasetUtilityGenerator generator = new TransactionDatasetUtilityGenerator();
			generator.convert(inputFile, outputFile, p1, p2);
			System.out
					.println("Transaction database with utility values generated.  ");
		}
		//
		else if ("Calculate_stats_for_a_sequence_database"
				.equals(algorithmName)) {
			SequenceStatsGenerator algo = new SequenceStatsGenerator();
			algo.getStats(inputFile);
		} else if ("Calculate_stats_for_a_transaction_database"
				.equals(algorithmName)) {
			TransactionStatsGenerator algo = new TransactionStatsGenerator();
			algo.getStats(inputFile);
		}

		// IF THE FILE WAS AN ARFF FILE, WE NEED TO CONVERT BACK THE RESULT
		// SO THAT IT IS PRESENTED IN TERMS OF VALUES
		if (mapItemAttributeValue != null) {
			ResultConverter converter = new ResultConverter();
			System.out
					.println("Post-processing to show result in terms of ARFF attribute values.");
			converter.convert(mapItemAttributeValue, outputFile,
					originalOutputFile);
			System.out.println("Post-processing completed.");
			// delete the temporary files
			// System.out.println("Delete : " + outputFile);
			File file = new File(outputFile);
			file.delete();
			// System.out.println("Delete : " + inputFile);
			File file2 = new File(inputFile);
			file2.delete();
			// set the original outputFile and inputFile
			outputFile = originalOutputFile;
			inputFile = originalInputFile;
		}
	}

	/**
	 * Method to convert a parameter given as a string to a double. For example,
	 * convert something like "50%" to 0.5.
	 * 
	 * @param value
	 *            a string
	 * @return a double
	 */
	private static double getParamAsDouble(String value) {
		if (value.contains("%")) {
			value = value.substring(0, value.length() - 1);
			return Double.parseDouble(value) / 100d;
		}
		return Double.parseDouble(value);
	}

	/**
	 * Method to transform a string to an integer
	 * 
	 * @param value
	 *            a string
	 * @return an integer
	 */
	private static int getParamAsInteger(String value) {
		return Integer.parseInt(value);
	}

	/**
	 * Method to get a parameter as a string. Note: this method just return the
	 * string taken as parameter.
	 * 
	 * @param value
	 *            a string
	 * @return a string
	 */
	private static String getParamAsString(String value) {
		return value;
	}

}
