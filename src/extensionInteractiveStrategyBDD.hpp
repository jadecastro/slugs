#ifndef __EXTENSION_INTERACTIVE_STRATEGY_HPP
#define __EXTENSION_INTERACTIVE_STRATEGY_HPP

#include <boost/algorithm/string.hpp>


/**
 * A class that opens an interactive shell to allow examining the property of strategies computed
 *
 */
template<class T> class XInteractiveStrategy : public T {
protected:
    XInteractiveStrategy<T>(std::list<std::string> &filenames) : T(filenames) {}

    using T::checkRealizability;
    using T::realizable;
    using T::variables;
    using T::variableNames;
    using T::variableTypes;
    using T::mgr;
    using T::winningPositions;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::safetyEnv;
    using T::safetySys;
    using T::strategyDumpingData;
    using T::varCubePostOutput;
    using T::varCubePre;
    using T::postOutputVars;
    using T::determinize;
    using T::initEnv;
    using T::initSys;
    using T::preVars;
    using T::postVars;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::doesVariableInheritType;
    using T::addVariable;

       
  std::string bddFileName;

public:
    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XInteractiveStrategy<T>(filenames);
    }

   /**
     * @brief init - Read input file(s)
     * @param filenames
     */
    void init(std::list<std::string> &filenames) {

        if (filenames.size()==0) {
            throw "Error: Cannot load SLUGS input file - there has been no input file name given!";
        }

        if (filenames.size()<2) {
            throw "Error: At least two file names are needed when using the supplied options!";
        }

        std::string specFileName = *(filenames.begin());
        filenames.pop_front();
        std::string bddFileName = *(filenames.begin());
        filenames.pop_front();

        std::ifstream inFile(specFileName.c_str());
        if (inFile.fail()) throw "Error: Cannot open input file";

    }

  
    void execute() {

      std::vector<int> counterVarNumbers;
      int goalTransitionSelectorVar;

      realizable = true;
       
        std::vector<BF> positionalStrategiesForTheIndividualGoals(livenessGuarantees.size());
	// Allocate counter variables
        for (unsigned int i=1;i<=livenessGuarantees.size();i = i << 1) {
            std::ostringstream os;
            os << "_jx_b" << counterVarNumbers.size();
            counterVarNumbers.push_back(addVariable(SymbolicStrategyCounterVar,os.str()));
        }
        goalTransitionSelectorVar = addVariable(SymbolicStrategyCounterVar,"strat_type");

	BF combinedStrategy =  mgr.readBDDFromFile(bddFileName.c_str(),variables);

	if (combinedStrategy == mgr.constantFalse()) {
	        realizable = false;
	}
 
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF thisEncoding = mgr.constantTrue();
            for (unsigned j=0;j<counterVarNumbers.size();j++) {
                if (j&(1 << i)) {
                    thisEncoding &= variables[counterVarNumbers[j]];
                } else {
                    thisEncoding &= !variables[counterVarNumbers[j]];
                }
            }
	    //positionalStrategiesForTheIndividualGoals[i] = combinedStrategy.ExistAbstract(thisEncoding & ((!variables[goalTransitionSelectorVar]) | livenessGuarantees[i]));
	    positionalStrategiesForTheIndividualGoals[i] = combinedStrategy & thisEncoding & ((!variables[goalTransitionSelectorVar]) | livenessGuarantees[i]);
	    
        }

	
        if (realizable) {

            BF currentPosition = mgr.constantFalse();
            unsigned int currentLivenessGuarantee = 0;

            while(true) {

                // The prompt
                std::cout << "> ";
                std::cout.flush();
                std::string command = "";
                while (command=="") {
                    std::getline(std::cin,command);
                    if (std::cin.eof()) return;
                }

                // Check the command
                boost::trim(command);
                boost::to_upper(command);

                if ((command=="QUIT") || (command=="EXIT")) {
                    return;
                } else if (command=="STARTPOS") {
                    BF initialPosition = winningPositions & initEnv & initSys;
                    assert(!(initialPosition.isFalse()));
                    initialPosition = determinize(initialPosition,preVars);
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (doesVariableInheritType(i, Pre)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            if ((variables[i] & initialPosition).isFalse()) {
                                std::cout << "0\n";
                            } else {
                                std::cout << "1\n";
                            }
                        }
                    }
                    currentPosition = initialPosition;
                } else if (command=="CHECKTRANS") {

                    std::cout << "From: \n";
                    BF from = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }

                    std::cout << "To: \n";
                    BF to = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PostInput) || (variableTypes[i]==PostOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }

                    std::cout << "Result: \n";
                    if ((from & winningPositions).isFalse()) {
                        std::cout << "- The pre-position is not winning.\n";
                    } else {
                        std::cout << "- The pre-position is winning.\n";
                    }
                    if ((from & to & safetyEnv).isFalse()) {
                        std::cout << "- The transition VIOLATES the SAFETY ASSUMPTIONS\n";
                    } else {
                        std::cout << "- The transition SATISFIES the SAFETY ASSUMPTIONS\n";
                    }
                    if ((from & to & safetySys).isFalse()) {
                        std::cout << "- The transition VIOLATES the SAFETY GUARANTEES\n";
                    } else {
                        std::cout << "- The transition SATISFIES the SAFETY GUARANTEES\n";
                    }
                    std::cout << "- The transition is a goal transition for the following liveness assumptions: ";
                    bool foundOne = false;
                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                        if (!(livenessAssumptions[i] & from & to).isFalse()) {
                            if (foundOne) std::cout << ", ";
                            foundOne = true;
                            std::cout << i;
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;
                    std::cout << "- The transition is a goal transition for the following liveness guarantees: ";
                    foundOne = false;
                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                        if (!(livenessGuarantees[i] & from & to).isFalse()) {
                            if (foundOne) std::cout << ", ";
                            foundOne = true;
                            std::cout << i;
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;

                    // Analyse if it is part of a possible strategy
                    std::cout << "- The transition is a possible transition in a strategy for the following goals: ";
                    foundOne = false;
                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                        if (!(positionalStrategiesForTheIndividualGoals[i] & from & to).isFalse()) {
                            if (foundOne) std::cout << ", ";
                            foundOne = true;
                            std::cout << i;
                        }
                    }
                    if (!foundOne) std::cout << "none";
                    std::cout << std::endl;

                } else if (command=="SETPOS") {

                    std::cout << "Position: \n";
                    BF from = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if ((variableTypes[i]==PreInput) || (variableTypes[i]==PreOutput)) {
                            std::cout << " - " << variableNames[i] << ": ";
                            std::cout.flush();
                            int value;
                            std::cin >> value;
                            if (std::cin.fail()) {
                                std::cout << "    -> Error reading value. Assuming 0.\n";
                                value = 0;
                            }
                            if (value==0) {
                                from &= !variables[i];
                            } else if (value==1) {
                                from &= variables[i];
                            } else {
                                std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                from &= variables[i];
                            }
                        }
                    }
                    currentPosition = from;
                } else if (command=="MOVE") {

                    if (currentPosition == mgr.constantFalse()) {
                        std::cout << "Error: The current position is undefined. Use SETPOS prior to calling MOVE." << std::endl;
                    } else {

                        std::cout << "Guarantee No.: ";
                        std::cout.flush();
                        unsigned int guarantee;
                        std::cin >> guarantee;
                        if (std::cin.fail()) {
                            std::cout << "    -> Error reading value. Aborting \n";
                        } else if (guarantee>=livenessGuarantees.size()) {
                            std::cout << "    -> Number too large. Aborting \n";
                        } else {

                            BF allowedInputs = (currentPosition & safetyEnv);
                            if (allowedInputs.isFalse()) {
                                std::cout << "No move possible. There is no allowed next input!\n";
                            } else {
                                BF_newDumpDot(*this,allowedInputs,"Pre Post","/tmp/allowedInputs.dot");

                                std::cout << "To: \n";
                                BF to = mgr.constantTrue();
                                BF nextPosition = mgr.constantTrue();
                                for (unsigned int i=0;i<variables.size();i++) {
                                    if (variableTypes[i]==PostInput) {
                                        std::cout << " - " << variableNames[i] << ": ";
                                        std::cout.flush();
                                        int value;
                                        std::cin >> value;
                                        if (std::cin.fail()) {
                                            std::cout << "    -> Error reading value. Assuming 0.\n";
                                            value = 0;
                                        }
                                        if (value==0) {
                                            to &= !variables[i];
                                            nextPosition &= !variables[i];
                                        } else if (value==1) {
                                            to &= variables[i];
                                            nextPosition &= variables[i];
                                        } else {
                                            std::cout << "    -> Value != 0 or 1. Assuming 1.\n";
                                            to &= variables[i];
                                        }
                                    }
                                }

                                // Simple check for sanity
                                if ((currentPosition & to & safetyEnv).isFalse()) {
                                    std::cout << "Warning: that is an illegal next input!\n";
                                }

                                // Compute which transition to takes
                                BF transition = currentPosition & to & positionalStrategiesForTheIndividualGoals[guarantee];


                                if (transition.isFalse()) {
                                    std::cout << "    -> Error: Input not allowed here.\n";
                                    if (!(currentPosition & to & safetyEnv).isFalse()) {
                                        std::cout << "       -> Actually, that's an internal error!\n";
                                    }
                                } else {

                                    transition = determinize(transition,postOutputVars);

                                    for (unsigned int i=0;i<variables.size();i++) {
                                        if (variableTypes[i]==PostOutput) {
                                            if ((variables[i] & transition).isFalse()) {
                                                std::cout << " - " << variableNames[i] << " = 0\n";
                                                nextPosition &= !variables[i];
                                            } else {
                                                std::cout << " - " << variableNames[i] << " = 1\n";
                                                nextPosition &= variables[i];
                                            }
                                        }
                                    }

                                    std::cout << "- The transition is a goal transition for the following liveness assumptions: ";
                                    bool foundOne = false;
                                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                                        if (!(livenessAssumptions[i] & transition).isFalse()) {
                                            if (foundOne) std::cout << ", ";
                                            foundOne = true;
                                            std::cout << i;
                                        }
                                    }
                                    if (!foundOne) std::cout << "none";
                                    std::cout << std::endl;
                                    std::cout << "- The transition is a goal transition for the following liveness guarantees: ";
                                    foundOne = false;
                                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                                        if (!(livenessGuarantees[i] & transition).isFalse()) {
                                            if (foundOne) std::cout << ", ";
                                            foundOne = true;
                                            std::cout << i;
                                        }
                                    }
                                    if (!foundOne) std::cout << "none";
                                    std::cout << std::endl;

                                    // Analyse if it is part of a possible strategy
                                    std::cout << "- The transition is a possible transition in a strategy for the following goals: ";
                                    foundOne = false;
                                    for (unsigned int i=0;i<livenessGuarantees.size();i++) {
                                        if (!(positionalStrategiesForTheIndividualGoals[i] & transition).isFalse()) {
                                            if (foundOne) std::cout << ", ";
                                            foundOne = true;
                                            std::cout << i;
                                        }
                                    }
                                    if (!foundOne) std::cout << "none";
                                    std::cout << std::endl;

                                    currentPosition = nextPosition.SwapVariables(varVectorPre,varVectorPost);
                                }
                            }
                        }
                    }
                }

                //========================================
                // Simplified functions to be called from
                // other tools.
                //========================================
                else if (command=="XMAKETRANS") {
                    std::cout << "\n"; // Get rid of the prompt
                    BF postInput = mgr.constantTrue();
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PostInput) {
                            char c;
                            std::cin >> c;
                            if (c=='0') {
                                postInput &= !variables[i];
                            } else if (c=='1') {
                                postInput &= variables[i];
                            } else {
                                std::cerr << "Error: Illegal XMAKETRANS string given.\n";
                            }
                        }
                    }
                    BF trans = currentPosition & postInput & safetyEnv;
                    if (trans.isFalse()) {
                        std::cout << "ERROR\n";
                        if (currentPosition.isFalse()) {
                        }
                    } else {
                        trans &= positionalStrategiesForTheIndividualGoals[currentLivenessGuarantee];

                        // Switching goals
                        BF newCombination = determinize(trans,postVars);

                        // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                        unsigned int nextLivenessGuarantee = currentLivenessGuarantee;
                        bool firstTry = true;
                        while (((nextLivenessGuarantee != currentLivenessGuarantee) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                            nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                            firstTry = false;
                        }

                        currentLivenessGuarantee = nextLivenessGuarantee;
                        currentPosition = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                        // Print position
                        for (unsigned int i=0;i<variables.size();i++) {
                            if (variableTypes[i]==PreInput) {
                                if ((variables[i] & currentPosition).isFalse()) {
                                    std::cout << "0";
                                } else {
                                    std::cout << "1";
                                }
                            }
                        }
                        for (unsigned int i=0;i<variables.size();i++) {
                            if (variableTypes[i]==PreOutput) {
                                if ((variables[i] & currentPosition).isFalse()) {
                                    std::cout << "0";
                                } else {
                                    std::cout << "1";
                                }
                            }
                        }
                        std::cout << "," << currentLivenessGuarantee << std::endl; // Flushes, too.
                    }
                    std::cout.flush();
                } else if (command=="XPRINTINPUTS") {
                    std::cout << "\n"; // Get rid of the prompt
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreInput)
                            std::cout << variableNames[i] << "\n";
                    }
                    std::cout << std::endl; // Flushes
                } else if (command=="XPRINTOUTPUTS") {
                    std::cout << "\n"; // Get rid of the prompt
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreOutput)
                            std::cout << variableNames[i] << "\n";
                    }
                    std::cout << std::endl; // Flushes
                } else if (command=="XGETINIT") {
                    std::cout << "\n"; // Get rid of the prompt
                    BF initialPosition = winningPositions & initEnv & initSys;
                    initialPosition = determinize(initialPosition,preVars);
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreInput) {
                            if ((variables[i] & initialPosition).isFalse()) {
                                std::cout << "0";
                            } else {
                                std::cout << "1";
                            }
                        }
                    }
                    for (unsigned int i=0;i<variables.size();i++) {
                        if (variableTypes[i]==PreOutput) {
                            if ((variables[i] & initialPosition).isFalse()) {
                                std::cout << "0";
                            } else {
                                std::cout << "1";
                            }
                        }
                    }
                    std::cout << ",0" << std::endl; // Flushes, too.
                    currentPosition = initialPosition;
                } else {
                    std::cout << "Error: Did not understand command '" << command << "'" << std::endl;
                }
            }
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }
    }


};


#endif
