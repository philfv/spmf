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
import java.awt.Desktop;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.util.Vector;

import javax.swing.ImageIcon;
import javax.swing.JButton;
import javax.swing.JCheckBox;
import javax.swing.JComboBox;
import javax.swing.JFileChooser;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;
import javax.swing.JPanel;
import javax.swing.JScrollPane;
import javax.swing.JTextArea;
import javax.swing.JTextField;
import javax.swing.border.EmptyBorder;

import ca.pfv.spmf.test.MainTestApriori_saveToFile;

/**
 * This class is the user interface of SPMF (the main Window).
 * It allows the user to launch single algorithms.
 * 
 * @author Philippe Fournier-Viger
 */
public class MainWindow extends JFrame {

    // variable for the current version of SPMF
    public static String SPMF_VERSION = "0.96r3";
    // current input file
    private String inputFile = null;
    // current output file
    private String outputFile = null;
    private static final long serialVersionUID = 1L;
    /**
     * The following fields are components of the user interface. They are
     * generated automatically by the Visual Editor plugin of Eclipse.
     */
    private JPanel contentPane;
    private JTextField textFieldParam1;
    private JTextField textFieldParam2;
    private JTextField textFieldParam3;
    private JTextField textFieldParam4;
    private JTextField textFieldParam5;
    private JTextField textFieldParam6;
    private JLabel labelParam1;
    private JLabel labelParam2;
    private JLabel labelParam3;
    private JLabel labelParam4;
    private JLabel labelParam5;
    private JLabel labelParam6;
    private JLabel lbHelp1;
    private JLabel lbHelp2;
    private JLabel lbHelp3;
    private JLabel lbHelp4;
    private JLabel lbHelp5;
    private JLabel lbHelp6;
    private JTextField textFieldInput;
    private JTextField textFieldOutput;
    private JComboBox<String> comboBox;
    private JTextArea textArea;
    private JButton buttonRun;
    private JCheckBox checkboxOpenOutput;
    private JButton buttonExample;
    private JLabel lblSetOutputFile;
    private JButton buttonOutput;
    private JButton buttonInput;
    private JLabel lblChooseInputFile;


    /**
     * Create the frame.
     */
    public MainWindow() {
        setResizable(false);
        addWindowListener(new WindowAdapter() {

            public void windowClosed(WindowEvent arg0) {
                System.exit(0);
            }
        });
        // set the title of the window
        setTitle("SPMF v" + SPMF_VERSION);

        // When the user clicks the "x" the software will close.
        setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
        // size of the window
        setBounds(100, 100, 706, 564);
        contentPane = new JPanel();
        contentPane.setBorder(new EmptyBorder(5, 5, 5, 5));
        setContentPane(contentPane);
        contentPane.setLayout(null);

        // Combo box to store the list of algorithms.
        comboBox = new JComboBox<String>(new Vector<String>());
        comboBox.setMaximumRowCount(20);
        comboBox.addItem("");
        comboBox.addItem("  ---- SEQUENTIAL PATTERN MINING ----");
        comboBox.addItem("BIDE+");
        comboBox.addItem("BIDE+_with_strings");
        comboBox.addItem("ClaSP");
        comboBox.addItem("CloSpan");
        comboBox.addItem("CM-SPADE");
        comboBox.addItem("CM-SPAM");
        comboBox.addItem("CM-ClaSP");
        comboBox.addItem("FEAT");
        comboBox.addItem("FSGP");
        comboBox.addItem("Fournier08-Closed+time");
        comboBox.addItem("GoKrimp");
        comboBox.addItem("GSP");
        comboBox.addItem("HirateYamana");
        comboBox.addItem("LAPIN");
        comboBox.addItem("MaxSP");
        comboBox.addItem("PrefixSpan");
        comboBox.addItem("PrefixSpan_AGP");
        comboBox.addItem("PrefixSpan_PostProcessingClosed");
        comboBox.addItem("PrefixSpan_with_strings");
        comboBox.addItem("SPADE");
        comboBox.addItem("SPADE_Parallelized");
        comboBox.addItem("SPAM");
        comboBox.addItem("SPAM_AGP");
        comboBox.addItem("SPAM_PostProcessingClosed");
        //comboBox.addItem("Fournier08-Closed+time+valued_items");
        comboBox.addItem("SeqDim_(PrefixSpan+Apriori)");
        comboBox.addItem("SeqDim_(PrefixSpan+Apriori)+time");
        comboBox.addItem("SeqDim_(BIDE+AprioriClose)");
        comboBox.addItem("SeqDim_(BIDE+AprioriClose)+time");
        comboBox.addItem("SeqDim_(BIDE+Charm)");
        comboBox.addItem("SeqDim_(BIDE+Charm)+time");
        comboBox.addItem("TKS");
        comboBox.addItem("TSP_nonClosed");
        comboBox.addItem("VGEN");
        comboBox.addItem("VMSP");
        comboBox.addItem("  ---- SEQUENTIAL RULE MINING ----");
        comboBox.addItem("CMRules");
        comboBox.addItem("CMDeo");
        comboBox.addItem("ERMiner");
        comboBox.addItem("RuleGen");
        comboBox.addItem("RuleGrowth");
        comboBox.addItem("TRuleGrowth");
        comboBox.addItem("TRuleGrowth_with_strings");
        comboBox.addItem("TopSeqRules");
        comboBox.addItem("TNS");
        comboBox.addItem("  ---- ITEMSET MINING----");
        comboBox.addItem("Apriori");
        comboBox.addItem("Apriori_with_hash_tree");
        comboBox.addItem("Apriori_TID");
        comboBox.addItem("Apriori_TID_bitset");
        comboBox.addItem("Apriori_TIDClose");
        comboBox.addItem("AprioriClose");
        comboBox.addItem("AprioriRare");
        comboBox.addItem("AprioriInverse");
        comboBox.addItem("CFPGrowth++");
        comboBox.addItem("Charm_bitset");
        comboBox.addItem("dCharm_bitset");
        comboBox.addItem("Charm_MFI");
        comboBox.addItem("DCI_Closed");
        comboBox.addItem("DefMe");
        comboBox.addItem("Eclat");
        comboBox.addItem("dEclat");
        comboBox.addItem("Eclat_bitset");
        comboBox.addItem("dEclat_bitset");
        comboBox.addItem("FHM");
        comboBox.addItem("FIN");
        comboBox.addItem("FPGrowth_itemsets");
        comboBox.addItem("FPGrowth_itemsets_with_strings");
        comboBox.addItem("HMine");
        comboBox.addItem("HUI-Miner");
        comboBox.addItem("IHUP");
        comboBox.addItem("LCM");
        comboBox.addItem("LCMFreq");
//        comboBox.addItem("LCMMax");
        comboBox.addItem("MSApriori");
        comboBox.addItem("Pascal");
        comboBox.addItem("PrePost");
        comboBox.addItem("Relim");
        comboBox.addItem("Two-Phase");
        comboBox.addItem("UApriori");
        comboBox.addItem("UPGrowth");
        comboBox.addItem("VME");
        comboBox.addItem("Zart");
        comboBox.addItem("  ---- ASSOCIATION RULE MINING ----");
        comboBox.addItem("Apriori_association_rules");
        comboBox.addItem("Closed_association_rules");
        comboBox.addItem("FHSAR");
        comboBox.addItem("FPGrowth_association_rules");
        comboBox.addItem("FPGrowth_association_rules_with_lift");
        comboBox.addItem("CFPGrowth++_association_rules");
        comboBox.addItem("CFPGrowth++_association_rules_with_lift");
        comboBox.addItem("IGB");
        comboBox.addItem("Indirect_association_rules");
        comboBox.addItem("MNR");
        comboBox.addItem("Sporadic_association_rules");
        comboBox.addItem("TopKRules");
        comboBox.addItem("TNR");
        comboBox.addItem("  ---- CLUSTERING ----");
        comboBox.addItem("Hierarchical_clustering");
        comboBox.addItem("KMeans");
        comboBox.addItem("  ---- DATASET TOOLS ----");
        comboBox.addItem("Calculate_stats_for_a_sequence_database");
        comboBox.addItem("Calculate_stats_for_a_transaction_database");
        comboBox.addItem("Convert_a_sequence_database_to_SPMF_format");
        comboBox.addItem("Convert_a_transaction_database_to_SPMF_format");
        comboBox.addItem("Convert_sequence_database_to_transaction_database");
        comboBox.addItem("Convert_transaction_database_to_sequence_database");
        comboBox.addItem("Generate_a_sequence_database");
        comboBox.addItem("Generate_a_sequence_database_with_timestamps");
        comboBox.addItem("Generate_a_transaction_database");
        comboBox.addItem("Generate_utility_values_for_transaction_database");
        comboBox.addItem("Add_consecutive_timestamps_to_sequence_database");
        comboBox.addItem("Fix_a_transaction_database");

        // What to do when the user choose an algorithm : 
        comboBox.addItemListener(new ItemListener() {
			@Override
			public void itemStateChanged(ItemEvent evt) {
				// We need to update the user interface:
				updateUserInterfaceAfterAlgorithmSelection(evt.getItem().toString(),
						evt.getStateChange() == ItemEvent.SELECTED);
			}
        	
        });
        comboBox.setBounds(263, 74, 367, 20);
        contentPane.add(comboBox);

        // The button "Run algorithm"
        buttonRun = new JButton("Run algorithm");
        buttonRun.setEnabled(false);
        buttonRun.addActionListener(new ActionListener() {

            public void actionPerformed(ActionEvent arg0) {

                // When the user clicks "run":
                processRunAlgorithmCommandFromGUI();

            }
        });
        buttonRun.setBounds(277, 340, 119, 23);
        contentPane.add(buttonRun);

        JLabel lblChooseAnAlgorithm = new JLabel("Choose an algorithm:");
        lblChooseAnAlgorithm.setBounds(22, 73, 204, 20);
        contentPane.add(lblChooseAnAlgorithm);

        JLabel lblNewLabel = new JLabel("New label");
        lblNewLabel.addMouseListener(new MouseAdapter() {

            @Override
            public void mousePressed(MouseEvent arg0) {
            	// Show the webpage of the SPMF project
                openWebPage("http://www.philippe-fournier-viger.com/spmf/");
            }
        });
        lblNewLabel.setIcon(new ImageIcon(MainWindow.class.getResource("spmf.png")));
        lblNewLabel.setBounds(12, 13, 140, 47);
        contentPane.add(lblNewLabel);

        textFieldParam1 = new JTextField();
        textFieldParam1.setBounds(263, 164, 157, 20);
        contentPane.add(textFieldParam1);
        textFieldParam1.setColumns(10);

        buttonInput = new JButton("...");
        buttonInput.addActionListener(new ActionListener() {

            public void actionPerformed(ActionEvent arg0) {
                askUserToChooseInputFile();
            }
        });
        
        buttonInput.setBounds(430, 104, 32, 23);
        contentPane.add(buttonInput);

        buttonOutput = new JButton("...");
        buttonOutput.addActionListener(new ActionListener() {

            public void actionPerformed(ActionEvent arg0) {
                askUserToChooseOutputFile();
            }
        });
        buttonOutput.setBounds(430, 133, 32, 23);
        contentPane.add(buttonOutput);

        labelParam1 = new JLabel("Parameter 1:");
        labelParam1.setBounds(22, 167, 204, 14);
        contentPane.add(labelParam1);

        labelParam2 = new JLabel("Parameter 2:");
        labelParam2.setBounds(22, 192, 204, 14);
        contentPane.add(labelParam2);

        labelParam3 = new JLabel("Parameter 3:");
        labelParam3.setBounds(22, 217, 204, 14);
        contentPane.add(labelParam3);

        labelParam4 = new JLabel("Parameter 4:");
        labelParam4.setBounds(22, 239, 231, 14);
        contentPane.add(labelParam4);

        labelParam5 = new JLabel("Parameter 5:");
        labelParam5.setBounds(22, 264, 231, 14);
        contentPane.add(labelParam5);

        labelParam6 = new JLabel("Parameter 6:");
        labelParam6.setBounds(22, 289, 231, 14);
        contentPane.add(labelParam6);

        textFieldParam2 = new JTextField();
        textFieldParam2.setColumns(10);
        textFieldParam2.setBounds(263, 189, 157, 20);
        contentPane.add(textFieldParam2);

        textFieldParam3 = new JTextField();
        textFieldParam3.setColumns(10);
        textFieldParam3.setBounds(263, 214, 157, 20);
        contentPane.add(textFieldParam3);

        textFieldParam4 = new JTextField();
        textFieldParam4.setColumns(10);
        textFieldParam4.setBounds(263, 236, 157, 20);
        contentPane.add(textFieldParam4);

        textFieldParam5 = new JTextField();
        textFieldParam5.setColumns(10);
        textFieldParam5.setBounds(263, 261, 157, 20);
        contentPane.add(textFieldParam5);

        textFieldParam6 = new JTextField();
        textFieldParam6.setColumns(10);
        textFieldParam6.setBounds(263, 286, 157, 20);
        contentPane.add(textFieldParam6);

        JScrollPane scrollPane = new JScrollPane();
        scrollPane.setBounds(10, 375, 681, 150);
        contentPane.add(scrollPane);

        textArea = new JTextArea();
        scrollPane.setViewportView(textArea);
        System.setOut(new PrintStream(new TextAreaOutputStream(textArea)));

        textFieldInput = new JTextField();
        textFieldInput.setEditable(false);
        textFieldInput.setBounds(263, 105, 157, 20);
        contentPane.add(textFieldInput);
        textFieldInput.setColumns(10);

        textFieldOutput = new JTextField();
        textFieldOutput.setEditable(false);
        textFieldOutput.setColumns(10);
        textFieldOutput.setBounds(263, 134, 157, 20);
        contentPane.add(textFieldOutput);

        checkboxOpenOutput = new JCheckBox("Open output file when the algorithm terminates");
        checkboxOpenOutput.setSelected(true);
        checkboxOpenOutput.setBounds(22, 310, 358, 23);
        contentPane.add(checkboxOpenOutput);

        buttonExample = new JButton("?");
        buttonExample.setEnabled(false);
        buttonExample.addActionListener(new ActionListener() {
            public void actionPerformed(ActionEvent arg0) {

                // When the user clicks on the "?",
                // we open the webpage corresponding to the algorithm
                // that is currently selected.
                String choice = (String) comboBox.getSelectedItem();
                openHelpWebPageForAlgorithm(choice);
            }

			
        });
        buttonExample.setBounds(642, 73, 49, 23);
        contentPane.add(buttonExample);

        lblChooseInputFile = new JLabel("Choose input file");
        lblChooseInputFile.setBounds(22, 108, 97, 14);
        contentPane.add(lblChooseInputFile);

        lblSetOutputFile = new JLabel("Set output file");
        lblSetOutputFile.setBounds(22, 137, 97, 14);
        contentPane.add(lblSetOutputFile);

        lbHelp1 = new JLabel("help1");
        lbHelp1.setBounds(430, 167, 157, 14);
        contentPane.add(lbHelp1);

        lbHelp2 = new JLabel("help2");
        lbHelp2.setBounds(430, 192, 157, 14);
        contentPane.add(lbHelp2);

        lbHelp3 = new JLabel("help3");
        lbHelp3.setBounds(430, 217, 157, 14);
        contentPane.add(lbHelp3);

        lbHelp4 = new JLabel("help4");
        lbHelp4.setBounds(430, 239, 157, 14);
        contentPane.add(lbHelp4);

        lbHelp5 = new JLabel("help5");
        lbHelp5.setBounds(430, 264, 157, 14);
        contentPane.add(lbHelp5);

        lbHelp6 = new JLabel("help6");
        lbHelp6.setBounds(430, 289, 157, 14);
        contentPane.add(lbHelp6);

        hideAllParams();
    }


    /**
     * This method updates the user interface according to what the user has selected or unselected
     * in the list of algorithms. For example, if the user choose the "PrefixSpan" algorithm
     * the parameters of the PrefixSpan algorithm will be shown in the user interface.
     * @param algorithmName  the algorithm name. 
     * @boolean isSelected indicate if the algorithm has been selected or unselected
     */
	private void updateUserInterfaceAfterAlgorithmSelection(String algorithmName, boolean isSelected) {
        // COMBOBOX ITEM SELECTION - ITEM STATE CHANGED
        if (isSelected) {
            buttonRun.setEnabled(true);
            buttonExample.setEnabled(true);

            if ("SPAM".equals(algorithmName)
                    || "PrefixSpan".equals(algorithmName)
                    || "FEAT".equals(algorithmName)
                    || "FSGP".equals(algorithmName)
                    || "VMSP".equals(algorithmName)
                    || "VGEN".equals(algorithmName)
                    ) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Max pattern length:", labelParam2, "(e.g. 4 items)");

            }else if ("CM-SPAM".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Min pattern length (optional):", labelParam2, "(e.g. 1 items)");
                setParam(textFieldParam3, "Max pattern length (optional):", labelParam3, "(e.g. 10 items)");
                setParam(textFieldParam4, "Required items (optional):", labelParam4, "(e.g. 1,2,3)");
            } 
            else if ("HirateYamana".equals(algorithmName)
                    || "Fournier08-Closed+time".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Min time interval:", labelParam2, "(e.g. 0 itemsets)");
                setParam(textFieldParam3, "Max time interval:", labelParam3, "(e.g. 2 itemsets)");
                setParam(textFieldParam4, "Min whole time interval:", labelParam4, "(e.g. 0 itemsets)");
                setParam(textFieldParam5, "Max whole time interval:", labelParam5, "(e.g. 2 itemsets)");

            } //					else if(
            //							"Fournier08-Closed+time+valued_items".equals(algorithmName))
            //					{
            //						// show the parameters of this algorithm
            //						hideAllParams(); 
            //						setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
            //						setParam(textFieldParam2, "Min time interval:", labelParam2, "(e.g. 0 itemsets)");
            //						setParam(textFieldParam3, "Max time interval:", labelParam3, "(e.g. 2 itemsets)");
            //						setParam(textFieldParam4, "Min whole time interval:", labelParam4, "(e.g. 0 itemsets)");
            //						setParam(textFieldParam5, "Max whole time interval:", labelParam5, "(e.g. 2 itemsets)");
            //						setParam(textFieldParam6, "Max whole time interval:", labelParam6, "(e.g. 2 )");
            //						setParam(textFieldParam7, "Max whole time interval:", labelP, "(e.g. 2 )");
            //						
            //					}
            //					comboBox.addItem("Fournier08-Closed+time");
            //					comboBox.addItem("Fournier08-Closed+time+valued_items");
            else if ("SeqDim_(PrefixSpan+Apriori)".equals(algorithmName)
                    || "SeqDim_(BIDE+AprioriClose)".equals(algorithmName)
                    || "SeqDim_(BIDE+Charm)".equals(algorithmName)
                    || "PrefixSpan_with_strings".equals(algorithmName)
                    || "BIDE+".equals(algorithmName)
                    || "BIDE+_with_strings".equals(algorithmName)
                    || "PrefixSpan_AGP".equals(algorithmName)
                    || "PrefixSpan_PostProcessingClosed".equals(algorithmName)
                    || "GSP".equals(algorithmName)
                    || "SPADE".equals(algorithmName)
                    || "CM-SPADE".equals(algorithmName)
                    || "CM-ClaSP".equals(algorithmName)
                    || "SPADE_Parallelized".equals(algorithmName)
                    || "SPAM_AGP".equals(algorithmName)
                    || "SPAM_PostProcessingClosed".equals(algorithmName)
                    || "ClaSP".equals(algorithmName)
                    || "CloSpan".equals(algorithmName)
                    || "LAPIN".equals(algorithmName)
                    || "MaxSP".equals(algorithmName)
                    || "FPGrowth_itemsets".equals(algorithmName)
                    || "FPGrowth_itemsets_with_strings".equals(algorithmName)
                    || "Apriori".equals(algorithmName)
                    || "Apriori_TID_bitset".equals(algorithmName)
                    || "Apriori_TID".equals(algorithmName)
                    || "Apriori_TIDClose".equals(algorithmName)
                    || "AprioriClose".equals(algorithmName)
                    || "AprioriRare".equals(algorithmName)
                    || "Eclat".equals(algorithmName)
                    || "dEclat".equals(algorithmName)
                    || "FIN".equals(algorithmName)
                    || "PrePost".equals(algorithmName)
                    || "Charm_MFI".equals(algorithmName)
                    || "Charm_bitset".equals(algorithmName)
                    || "dCharm_bitset".equals(algorithmName)
                    || "dEclat_bitset".equals(algorithmName)
                    || "Relim".equals(algorithmName)
                    || "Eclat_bitset".equals(algorithmName)
                    || "LCM".equals(algorithmName)
                    || "LCMFreq".equals(algorithmName)
                    || "LCMMax".equals(algorithmName)
                    || "Pascal".equals(algorithmName)
                    || "DefMe".equals(algorithmName)
                    || "Zart".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.4 or 40%)");
            } else if ("Apriori_with_hash_tree".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.4 or 40%)");
                setParam(textFieldParam2, "Hash-tree branch count:", labelParam2, "(default: 30)");
            } else if ("SeqDim_(PrefixSpan+Apriori)+time".equals(algorithmName)
                    || "SeqDim_(BIDE+AprioriClose)+time".equals(algorithmName)
                    || "SeqDim_(BIDE+Charm)+time".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g.  0.5  or 50 %)");
                setParam(textFieldParam2, "Choose minInterval:", labelParam2, "(e.g.  1)");
                setParam(textFieldParam3, "Choose maxInterval:", labelParam3, "(e.g.  5)");
                setParam(textFieldParam4, "Choose minWholeInterval:", labelParam4, "(e.g.  1)");
                setParam(textFieldParam5, "Choose maxWholeInterval:", labelParam5, "(e.g.  5)");
            } else if ("HMine".equals(algorithmName)
                    || "DCI_Closed".equals(algorithmName)
                    ) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (integer):", labelParam1, "(e.g. 2)");
            } else if ("VME".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose threshold (%):", labelParam1, "(e.g. 0.15 or 15%)");
            } else if ("AprioriInverse".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.001 or 0.1%)");
                setParam(textFieldParam2, "Choose maxsup (%):", labelParam2, "(e.g. 0.06 or 6%)");
            } else if ("UApriori".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose expected support (%):", labelParam1, "(e.g. 0.10)");
            } else if ("FPGrowth_association_rules".equals(algorithmName)
                    || "Apriori_association_rules".equals(algorithmName)
                    || "ERMiner".equals(algorithmName)
                    || "CMRules".equals(algorithmName)
                    || "CMDeo".equals(algorithmName)
                    || "IGB".equals(algorithmName)
                    || "Closed_association_rules".equals(algorithmName)
                    || "MNR".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
            }else if ("RuleGrowth".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam3, "Max antecedent size (optional):", labelParam3, "(e.g. 1 items)");
                setParam(textFieldParam4, "Max consequent size (optional):", labelParam4, "(e.g. 2 items)");
            }//
            else if ("Sporadic_association_rules".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.1 or 10%)");
                setParam(textFieldParam2, "Choose maxsup (%):", labelParam2, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam3, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
            } else if ("Indirect_association_rules".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam2, "Choose ts (%):", labelParam2, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam3, "Choose minconf (%):", labelParam2, "(e.g. 0.1 or 10%)");
            } else if ("RuleGen".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (integer):", labelParam1, "(e.g. 3)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
            } else if ("KMeans".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose K:", labelParam1, "(e.g. 3)");
            } else if ("Hierarchical_clustering".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose max distance:", labelParam1, "(e.g. 4)");
            } else if ("FPGrowth_association_rules_with_lift".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam3, "Choose minlift:", labelParam3, "(e.g. 0.2)");
            } else if ("CFPGrowth++_association_rules_with_lift".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "MIS file name:", labelParam1, "(e.g. MIS.txt)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam3, "Choose minlift:", labelParam3, "(e.g. 0.2)");
            } else if ("CFPGrowth++_association_rules".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "MIS file name:", labelParam1, "(e.g. MIS.txt)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
            } 
            else if ("TopSeqRules".equals(algorithmName)
                    || "TopKRules".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose k:", labelParam1, "(e.g. 3)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.8 or 80%)");
            } else if ("TSP_nonClosed".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose k:", labelParam1, "(e.g. 5)");
            }else if ("TKS".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose k:", labelParam1, "(e.g. 5)");
                setParam(textFieldParam2, "Min pattern length (optional):", labelParam2, "(e.g. 1 items)");
                setParam(textFieldParam3, "Max pattern length (optional):", labelParam3, "(e.g. 10 items)");
                setParam(textFieldParam4, "Required items (optional):", labelParam4, "(e.g. 1,2,3)");
            }else if ("TNR".equals(algorithmName) || "TNS".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose k:", labelParam1, "(e.g. 10)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam3, "Choose delta:", labelParam3, "(e.g. 2)");
            } else if ("Two-Phase".equals(algorithmName) || "HUI-Miner".equals(algorithmName)
            		|| "FHM".equals(algorithmName)
            		|| "IHUP".equals(algorithmName)
            		|| "UPGrowth".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minutility:", labelParam1, "(e.g. 30)");
            } else if ("FHSAR".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.5 or 50%)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.6 or 60%)");
                setParam(textFieldParam3, "SAR file name:", labelParam3, "(e.g. sar.txt)");

            } else if ("GoKrimp".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Label file name (optional:", labelParam1, "(e.g. test_goKrimp.lab)");
            } 
            else if ("MSApriori".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose beta:", labelParam1, "(e.g. 0.4 or 40%)");
                setParam(textFieldParam2, "Choose LS:", labelParam2, "(e.g. 0.2 or 20%)");
            } else if ("CFPGrowth++".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "MIS file name:", labelParam1, "(e.g. MIS.txt)");
            } else if ("TRuleGrowth".equals(algorithmName)
                    || "TRuleGrowth_with_strings".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose minsup (%):", labelParam1, "(e.g. 0.7 or 70%)");
                setParam(textFieldParam2, "Choose minconf (%):", labelParam2, "(e.g. 0.8 or 80%)");
                setParam(textFieldParam3, "Choose window_size:", labelParam3, "(e.g. 3)");
                setParam(textFieldParam4, "Max antecedent size (optional):", labelParam4, "(e.g. 1 items)");
                setParam(textFieldParam5, "Max consequent size (optional):", labelParam5, "(e.g. 2 items)");
            } else if ("Convert_a_sequence_database_to_SPMF_format".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose input format:", labelParam1, "(e.g. CSV_INTEGER)");
                setParam(textFieldParam2, "Choose sequence count:", labelParam2, "(e.g. 5)");
            } //Convert_a_transaction_database_to_SPMF_format
            else if ("Convert_a_transaction_database_to_SPMF_format".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose input format:", labelParam1, "(e.g. CSV_INTEGER)");
                setParam(textFieldParam2, "Choose sequence count:", labelParam2, "(e.g. 5)");
            } else if ("Convert_sequence_database_to_transaction_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose transaction count:", labelParam1, "(e.g. 5)");
            } else if ("Convert_transaction_database_to_sequence_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose sequence count:", labelParam1, "(e.g. 5)");
            } else if ("Fix_a_transaction_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
            } 
            else if ("Generate_a_sequence_database".equals(algorithmName)
                    || "Generate_a_sequence_database_with_timestamps".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose sequence count:", labelParam1, "(e.g. 100)");
                setParam(textFieldParam2, "Choose max. distinct items:", labelParam2, "(e.g. 1000)");
                setParam(textFieldParam3, "Choose item count by itemset:", labelParam3, "(e.g. 3)");
                setParam(textFieldParam4, "Choose itemset count per sequence:", labelParam4, "(e.g. 7)");
                lblChooseInputFile.setVisible(false);
                buttonInput.setVisible(false);
                textFieldInput.setVisible(false);
            } else if ("Add_consecutive_timestamps_to_sequence_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
            } 
            else if ("Generate_a_transaction_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose transaction count:", labelParam1, "(e.g. 100)");
                setParam(textFieldParam2, "Choose max. distinct items:", labelParam2, "(e.g. 1000)");
                setParam(textFieldParam3, "Max. item count per transaction:", labelParam3, "(e.g. 10)");
                lblChooseInputFile.setVisible(false);
                buttonInput.setVisible(false);
                textFieldInput.setVisible(false);
            } else if ("Generate_utility_values_for_transaction_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                setParam(textFieldParam1, "Choose max quantity:", labelParam1, "(e.g. 10)");
                setParam(textFieldParam2, "Choose multiplicative factor:", labelParam2, "(e.g. 4)");
                lblChooseInputFile.setVisible(false);
                buttonInput.setVisible(false);
                textFieldInput.setVisible(false);
            } 
            //Generate_utility_values_for_transaction_database
            else if ("Calculate_stats_for_a_sequence_database".equals(algorithmName) ||
            		"Calculate_stats_for_a_transaction_database".equals(algorithmName)) {
                // show the parameters of this algorithm
                hideAllParams();
                lblSetOutputFile.setVisible(false);
                buttonOutput.setVisible(false);
                textFieldOutput.setVisible(false);
                checkboxOpenOutput.setVisible(false);
            } else {
                // This is for the command line version
                // If the name of the algorithm is not recognized:
                if (isVisible() == false) {
                    System.out.println("There is no algorithm with this name. "
                            + " To fix this problem, you may check the command syntax in the SPMF documentation"
                            + " and/or verify if there is a new version of SPMF on the SPMF website.");
                }

                hideAllParams();
                buttonRun.setEnabled(false);
                buttonExample.setEnabled(false);
            }
        } else {
            // if no algorithm is chosen, we hide all parameters.
            hideAllParams();
            buttonRun.setEnabled(false);
            buttonExample.setEnabled(false);
        }
	}

    private  void setParam(JTextField textfield, String name, JLabel label, String helpText) {
        label.setText(name);
        textfield.setEnabled(true);
        textfield.setVisible(true);
        label.setVisible(true);
        if (textfield == textFieldParam1) {
            lbHelp1.setText(helpText);
            lbHelp1.setVisible(true);
        } else if (textfield == textFieldParam2) {
            lbHelp2.setText(helpText);
            lbHelp2.setVisible(true);
        } else if (textfield == textFieldParam3) {
            lbHelp3.setText(helpText);
            lbHelp3.setVisible(true);
        } else if (textfield == textFieldParam4) {
            lbHelp4.setText(helpText);
            lbHelp4.setVisible(true);
        } else if (textfield == textFieldParam5) {
            lbHelp5.setText(helpText);
            lbHelp5.setVisible(true);
        } else if (textfield == textFieldParam6) {
            lbHelp6.setText(helpText);
            lbHelp6.setVisible(true);
        }
    }

//    private  static void setHelpTextForParam(JLabel label, String name) {
//        label.setText(name);
//        label.setVisible(true);
//    }


    /**
     * Hide all parameters from the user interface. This is used to hide fields
     * when the user change algorithms or when the JFrame is first created.
     */
    private  void hideAllParams() {
        labelParam1.setVisible(false);
        labelParam2.setVisible(false);
        labelParam3.setVisible(false);
        labelParam4.setVisible(false);
        labelParam5.setVisible(false);
        labelParam6.setVisible(false);
//		.setVisible(false);
        lbHelp1.setVisible(false);
        lbHelp2.setVisible(false);
        lbHelp3.setVisible(false);
        lbHelp4.setVisible(false);
        lbHelp5.setVisible(false);
        lbHelp6.setVisible(false);
        textFieldParam1.setVisible(false);
        textFieldParam2.setVisible(false);
        textFieldParam3.setVisible(false);
        textFieldParam4.setVisible(false);
        textFieldParam5.setVisible(false);
        textFieldParam6.setVisible(false);

        lblSetOutputFile.setVisible(true);
        buttonOutput.setVisible(true);
        textFieldOutput.setVisible(true);
        lblChooseInputFile.setVisible(true);
        buttonInput.setVisible(true);
        textFieldInput.setVisible(true);


        checkboxOpenOutput.setVisible(true);
    }

    static class TextAreaOutputStream extends OutputStream {

        JTextArea textArea;

        public TextAreaOutputStream(JTextArea textArea) {
            this.textArea = textArea;
        }

        public void flush() {
            textArea.repaint();
        }

        public void write(int b) {
            textArea.append(new String(new byte[]{(byte) b}));
        }
    }


    /**
     * This method open a URL in the default web browser.
     *
     * @param url : URL of the webpage
     */
    private void openWebPage(String url) {
        try {
            java.awt.Desktop.getDesktop().browse(java.net.URI.create(url));
        } catch (java.io.IOException e) {
            System.out.println(e.getMessage());
        }
    }

    /**
     * This method show the help webpage for a given algorithm in the default browser of the user.
     * @param choice the algorithm name (e.g. "PrefixSpan")
     */
    private void openHelpWebPageForAlgorithm(String choice) {
		if ("PrefixSpan".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#examplePrefixSpan");
        } else if ("HirateYamana".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example11");
        } else if ("PrefixSpan_with_strings".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#examplePrefixSpan");
        } else if ("SeqDim_(PrefixSpan+Apriori)".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#exampleMDSPM1");
        } else if ("SeqDim_(BIDE+AprioriClose)".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#exampleMDSPM1");
        } else if ("SeqDim_(BIDE+Charm)".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#exampleMDSPM1");
        } else if ("SeqDim_(PrefixSpan+Apriori)+time".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example14");
        } else if ("SeqDim_(BIDE+AprioriClose)+time".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example14");
        } else if ("SeqDim_(BIDE+Charm)+time".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example14");
        } else if ("SPAM".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#spam");
        } else if ("BIDE+".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#exampleBIDE");
        } else if ("BIDE+_with_strings".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#exampleBIDE");
        } else if ("RuleGrowth".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#rulegrowth");
        }  else if ("ERMiner".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#erminer");
        } else if ("TRuleGrowth".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#trulegrowth");
        } else if ("TRuleGrowth_with_strings".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#trulegrowth");
        } else if ("CMRules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cmrules");
        } else if ("CMDeo".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cmdeo");
        }//Sporadic_association_rules
        else if ("Sporadic_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example19");
        }// Closed_association_rules
        else if ("Closed_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example20");
        } //IGB
        else if ("IGB".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example7");
        }// MNR
        else if ("MNR".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example21");
        } //Indirect_association_rules
        else if ("Indirect_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#indirect");
        } else if ("RuleGen".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#rulegen");
        } else if ("TopSeqRules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#topseqrules");
        } else if ("TopKRules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#topkrules");
        } else if ("TNR".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#tnr");
        } else if ("FPGrowth_itemsets".equals(choice) || "FPGrowth_itemsets_with_strings".equals("choice")) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#growth");
        } else if ("Apriori_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#allassociationrules");
        } else if ("FPGrowth_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#allassociationrules");
        } else if ("FPGrowth_association_rules_with_lift".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#lift");
        }else if ("CFPGrowth++_association_rules".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cfpgrowth_ar");
        } else if ("CFPGrowth++_association_rules_with_lift".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cfpgrowth_ar");
        } else if ("Apriori".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example1");
        } else if ("Apriori_with_hash_tree".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example1");
        } else if ("AprioriClose".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example2");
        } else if ("Apriori_TID".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example2");
        } else if ("Apriori_TIDClose".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example2");
        } else if ("AprioriRare".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example17");
        } else if ("AprioriInverse".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example18");
        } else if ("VME".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#erasable");
        } else if ("UApriori".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#uapriori");
        } else if ("MSApriori".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#msapriori");
        } else if ("CFPGrowth++".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cfpgrowth");
        } else if ("Apriori_TID_bitset".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#aprioritid");
        } else if ("HMine".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#hmine");
        } else if ("DCI_Closed".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#dciclosed");
        } else if ("DefMe".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#defme");
        } else if ("Charm_MFI".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e3");
        } else if ("dCharm_bitset".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e2");
        } else if ("Charm_bitset".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e2");
        } else if ("Eclat".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e1");
        }  else if ("dEclat".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e1");
        }  else if ("dEclat_bitset".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e1");
        } else if ("Eclat_bitset".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#e1");
        } else if ("Relim".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#c23");
        } else if ("Zart".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#zart");
        } else if ("Pascal".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#pascal");
        } else if ("LCM".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#LCM");
        }
        else if ("LCMFreq".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#LCMFreq");
        }else if ("LCMMax".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#LCMFreq");
        }
        else if ("Two-Phase".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#twophase");
        } else if ("HUI-Miner".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#huiminer");
        }  else if ("FHM".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#fhm");
        } else if ("FHSAR".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#FHSAR");
        } else if ("KMeans".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example8");
        } else if ("Hierarchical_clustering".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example10");
        } else if ("Convert_a_sequence_database_to_SPMF_format".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#convseq");
        } else if ("Convert_a_transaction_database_to_SPMF_format".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#convtdb");
        } else if ("Convert_sequence_database_to_transaction_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#convseqtrans");
        } else if ("Convert_transaction_database_to_sequence_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#convtransseq");
        } 
        else if ("Generate_a_sequence_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#genseq");
        } else if ("Add_consecutive_timestamps_to_sequence_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#addtimestamps");
        } else if ("Generate_a_sequence_database_with_timestamps".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#genseqt");
        } else if ("Generate_a_transaction_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#gentrans");
        }else if ("Fix_a_transaction_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#fixtdb");
        }else if ("Generate_utility_values_for_transaction_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#genutilvalues");
        }
        else if ("Calculate_stats_for_a_sequence_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#statsseq");
        } else if ("Calculate_stats_for_a_transaction_database".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#stattrans");
        } else if ("TNS".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#tns");
        } else if ("TNR".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#tnr");
        } else if ("CM-SPAM".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cmspam");
        } else if ("CM-SPADE".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cmspade");
        }else if ("CM-ClaSP".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#cmclasp");
        } else if ("MaxSP".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#maxsp");
        }else if ("VMSP".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#vmsp");
        } else if ("TKS".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#tks");
        }else if ("TSP_nonClosed".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#tsp");
        }else if ("VGEN".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#vgen");
        }else if ("FEAT".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#feat");
        }else if ("FSGP".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#fsgp");
        }else if ("LAPIN".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#lapin");
        }else if ("Fournier08-Closed+time".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#example12");
        }else if ("UPGrowth".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#upgrowth");
        }else if ("IHUP".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#ihup");
        }else if ("FIN".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#FIN");
        }else if ("PrePost".equals(choice)) {
            openWebPage("http://www.philippe-fournier-viger.com/spmf/index.php?link=documentation.php#PrePost");
        }
	}

    /**
     * This method ask the user to choose the input file. This method is
     * called when the user click on the button to choose the input file.
     */
	private void askUserToChooseInputFile() {
		try {
		    // WHEN THE USER CLICK TO CHOOSE THE INPUT FILE

		    File path;
		    // Get the last path used by the user, if there is one
		    String previousPath = PathsManager.getInstance().getInputFilePath();
		    if (previousPath == null) {
		        // If there is no previous path (first time user), 
		        // show the files in the "examples" package of
		        // the spmf distribution.
		        URL main = MainTestApriori_saveToFile.class.getResource("MainTestApriori_saveToFile.class");
		        if (!"file".equalsIgnoreCase(main.getProtocol())) {
		            path = null;
		        } else {
		            path = new File(main.getPath());
		        }
		    } else {
		        // Otherwise, the user used SPMF before, so
		        // we show the last path that he used.
		        path = new File(previousPath);
		    }

		    // Create a file chooser to let the user
		    // select the file.
		    final JFileChooser fc = new JFileChooser(path);
		    fc.setFileSelectionMode(JFileChooser.FILES_ONLY);
		    int returnVal = fc.showOpenDialog(MainWindow.this);

		    // if he chose a file
		    if (returnVal == JFileChooser.APPROVE_OPTION) {
		        File file = fc.getSelectedFile();
		        textFieldInput.setText(file.getName());
		        inputFile = file.getPath(); // remember the file he chose
		    }
		    // remember this folder for next time.
		    if (fc.getSelectedFile() != null) {
		        PathsManager.getInstance().setInputFilePath(fc.getSelectedFile().getParent());
		    }
		} catch (Exception e) {
		    JOptionPane.showMessageDialog(null,
		            "An error occured while opening the input file dialog. ERROR MESSAGE = " + e.toString(), "Error",
		            JOptionPane.ERROR_MESSAGE);
		}
	}

    /**
     * This method ask the user to choose the output file. This method is
     * called when the user click on the button to choose the input file.
     */
	private void askUserToChooseOutputFile() {
		try {
		    // WHEN THE USER CLICK TO CHOOSE THE OUTPUT FILE

		    File path;
		    // Get the last path used by the user, if there is one
		    String previousPath = PathsManager.getInstance().getOutputFilePath();
		    // If there is no previous path (first time user), 
		    // show the files in the "examples" package of
		    // the spmf distribution.
		    if (previousPath == null) {
		        URL main = MainTestApriori_saveToFile.class.getResource("MainTestApriori_saveToFile.class");
		        if (!"file".equalsIgnoreCase(main.getProtocol())) {
		            path = null;
		        } else {
		            path = new File(main.getPath());
		        }
		    } else {
		        // Otherwise, use the last path used by the user.
		        path = new File(previousPath);
		    }

		    // ASK THE USER TO CHOOSE A FILE
		    final JFileChooser fc;
		    if (path != null) {
		        fc = new JFileChooser(path.getAbsolutePath());
		    } else {
		        fc = new JFileChooser();
		    }
		    int returnVal = fc.showSaveDialog(MainWindow.this);

		    // If the user chose a file
		    if (returnVal == JFileChooser.APPROVE_OPTION) {
		        File file = fc.getSelectedFile();
		        textFieldOutput.setText(file.getName());
		        outputFile = file.getPath(); // save the file path
		        // save the path of this folder for next time.
		        if (fc.getSelectedFile() != null) {
		            PathsManager.getInstance().setOutputFilePath(fc.getSelectedFile().getParent());
		        }
		    }

		} catch (Exception e) {
		    JOptionPane.showMessageDialog(null,
		            "An error occured while opening the output file dialog. ERROR MESSAGE = " + e.toString(), "Error",
		            JOptionPane.ERROR_MESSAGE);
		}
	}

	/**
	 * This method is called when the user click the "Run" button of the user interface,
	 * to launch the chosen algorithm and thereafter catch exception if one occurs.
	 */
	private void processRunAlgorithmCommandFromGUI() {
		// Get the parameters
		String choice = (String) comboBox.getSelectedItem();
		String parameters[] = new String[6];
		parameters[0] = textFieldParam1.getText();
		parameters[1] = textFieldParam2.getText();
		parameters[2] = textFieldParam3.getText();
		parameters[3] = textFieldParam4.getText();
		parameters[4] = textFieldParam5.getText();
		parameters[5] = textFieldParam6.getText();
		textArea.setText("");

		boolean succeed = false;
		try {
			// RUN THE SELECTED ALGORITHM
			CommandProcessor.runAlgorithm(choice, inputFile, outputFile, parameters);  // END IF - CHECBOX
			succeed = true;
		}catch (NumberFormatException e) {
            JOptionPane.showMessageDialog(null,
                    "Error. Please check the parameters of the algorithm.  The format for numbers is incorrect. \n"
                    + "\n ERROR MESSAGE = " + e.toString(), "Error",
                    JOptionPane.ERROR_MESSAGE);
        } catch (Throwable e) {
            JOptionPane.showMessageDialog(null,
                    "An error while trying to run the algorithm. \n ERROR MESSAGE = " + e.toString(), "Error",
                    JOptionPane.ERROR_MESSAGE);
            e.printStackTrace();
        }

		// IF - the algorithm terminates...
		if (succeed && checkboxOpenOutput.isSelected() && lblSetOutputFile.isVisible()) {
		    // open the output file if the checkbox is checked 
		    Desktop desktop = Desktop.getDesktop();
		    // check first if we can open it on this operating system:
		    if (desktop.isSupported(Desktop.Action.OPEN)) {
		        try {
		            // if yes, open it
		            desktop.open(new File(outputFile));
		        } catch (IOException e) {
		            JOptionPane.showMessageDialog(null,
		                    "The output file failed to open with the default application. "
		                    + "\n This error occurs if there is no default application on your system "
		                    + "for opening the output file or the application failed to start. "
		                    + "\n\n"
		                    + "To fix the problem, consider changing the extension of the output file to .txt."
		                    + "\n\n ERROR MESSAGE = " + e.toString(), "Error",
		                    JOptionPane.ERROR_MESSAGE);
		        } catch (SecurityException e) {
		            JOptionPane.showMessageDialog(null,
		                    "A security error occured while trying to open the output file. ERROR MESSAGE = " + e.toString(), "Error",
		                    JOptionPane.ERROR_MESSAGE);
		        } catch (Throwable e) {
		            JOptionPane.showMessageDialog(null,
		                    "An error occured while opening the output file. ERROR MESSAGE = " + e.toString(), "Error",
		                    JOptionPane.ERROR_MESSAGE);
		        }
		    }
		}
	}
}
