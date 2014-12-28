#ifndef __EXTENSION_REFINE_ASSUMPTIONS_HPP
#define __EXTENSION_REFINE_ASSUMPTIONS_HPP

#include "gr1context.hpp"
#include <map>
#include <string>

/**
 * This extension modifies the execute() function ...
 */
template<class T> class XRefineAssumptions : public T {
protected:

    // New variables
    std::string outputFilenameStrategy;

    // Inherit stuff that we actually use here.
    using T::realizable;
    using T::variables;
    using T::variableTypes;
    using T::variableNames;
    using T::checkRealizability;
    using T::determinize;
    using T::doesVariableInheritType;
    using T::mgr;
    using T::varCubePre;
    using T::varCubePost;
    using T::varCubePostInput;
    using T::varCubePostOutput;
    using T::varCubePreInput;
    using T::varCubePreOutput;
    using T::preVars;
    using T::postVars;
    using T::postOutputVars;
    using T::livenessAssumptions;
    using T::livenessGuarantees;
    using T::safetyEnv;
    using T::safetySys;
    using T::initEnv;
    using T::initSys;
    using T::varVectorPre;
    using T::varVectorPost;
    using T::strategyDumpingData;
    using T::winningPositions;

    std::vector<std::pair<unsigned int,BF> > strategyDumpingDataPlayer2;
    BF winningPositionsPlayer2;
    bool initSpecialRoboticsSemantics = false;

    SlugsVectorOfVarBFs preInputVars{PreInput,this};
    SlugsVectorOfVarBFs postInputVars{PostInput,this};

    BF failingPreAndPostConditions = mgr.constantFalse();
    std::vector<boost::tuple<unsigned int,BF> > foundCutConditions;

public:

    XRefineAssumptions<T>(std::list<std::string> &filenames) : T(filenames) {
        if (filenames.size()==1) {
            outputFilenameStrategy = "";
        } else {
            outputFilenameStrategy = filenames.front();
            filenames.pop_front();
        }
    }

    void execute() {
        T::execute();
        if (!realizable) {
            extractPatternsFromWinningStates();
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysBefore.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvBefore.dot");

        // for (unsigned int i=0;i<livenessAssumptions.size();i++) {
        //     std::stringstream fname;
        //     fname << "/tmp/livenessAssumptionsBefore" << i << ".dot";
        //     BF_newDumpDot(*this,livenessAssumptions[i],NULL,fname.str());
        // }
        // for (unsigned int i=0;i<livenessGuarantees.size();i++) {
        //     std::stringstream fname;
        //     fname << "/tmp/livenessGuaranteesBefore" << i << ".dot";
        //     BF_newDumpDot(*this,livenessGuarantees[i],NULL,fname.str());
        // }

        int iter = 0;
        while (!failingPreAndPostConditions.isFalse()){ // & idx<=10){
            std::cerr << "adding safety assumptions/guarantees and re-synthesizing the counter-strategy\n";
            std::cerr << "major iter " << iter << "\n";
            std::stringstream fname;
            fname << "/tmp/failingPreAndPostConditions" << iter << ".dot";
            BF_newDumpDot(*this,failingPreAndPostConditions,NULL,fname.str());
            std::stringstream fname1;
            fname1 << "/tmp/safetySysBefore" << iter << ".dot";
            BF_newDumpDot(*this,safetySys,NULL,fname1.str());
            std::stringstream fname2;
            fname2 << "/tmp/safetyEnvBefore" << iter << ".dot";
            BF_newDumpDot(*this,safetyEnv,NULL,fname2.str());
            // BF_newDumpDot(*this,foundCutPostConditions,NULL,"/tmp/candidateWinningPreConditionsBefore.dot");

            BF TODO = failingPreAndPostConditions;
            int idx = 0;
            int counter = 0;
            bool foundRevisions = false;
            std::vector<double> xDecimalValue;
            std::vector<double> yDecimalValue;
            BF safetyEnvTent = mgr.constantTrue();
            BF safetySysTent = mgr.constantTrue();
            while (!TODO.isFalse()){
                BF deadAssignment = determinize(TODO,preOutputVars);
                TODO &= !deadAssignment;

                BF deadlockPre = deadAssignment.ExistAbstract(varCubePost);
                BF deadlockPost = deadAssignment.ExistAbstract(varCubePre);

                BF candidateEnvTrans = deadlockPre.Implies(!deadlockPost);
                BF candidateSysTrans = deadlockPost.Implies(!deadlockPre.SwapVariables(varVectorPre,varVectorPost));

                if (((safetyEnv.ExistAbstract(varCubePostInput)) & !((safetyEnv & candidateEnvTrans).ExistAbstract(varCubePostInput))).isFalse()) {
                    foundRevisions = true;
                    safetyEnvTent &= candidateEnvTrans;
                    safetySysTent &= candidateSysTrans;

                    BF flaggedMotion = deadlockPre.ExistAbstract(varCubePreOutput);

                    // std::stringstream fname3;
                    // fname3 << "/tmp/addedSafetyEnv" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,candidateEnvTrans,NULL,fname3.str());
                    // std::stringstream fname4;
                    // fname4 << "/tmp/addedSafetySys" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,candidateSysTrans,NULL,fname4.str());
                    // std::stringstream fname3;
                    // fname3 << "/tmp/safetyEnvAfter" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,safetyEnv,NULL,fname3.str());
                    // std::stringstream fname4;
                    // fname4 << "/tmp/safetySysAfter" << iter << "index" << idx << ".dot";
                    // BF_newDumpDot(*this,safetySys,NULL,fname4.str());
                    
                    // std::cerr << idx << " ";
                    counter++;
                }
                idx++;
            }

            if (!foundRevisions) {throw SlugsException(false,"Error: could not find any refinements!\n");}
            std::cerr << "\n";

            // std::cerr << "Deadlock revisions found.\nWhen within " << maxDist << " of station_1, never set environment variable s1_occupied to True.\nAccept? (y/n)";
            char userResponse = 'y';
            // std::cin >> userResponse;
            if (userResponse == 'y') {
                safetySys &= safetySysTent;
                safetyEnv &= safetyEnvTent;
            }

            // prepare the variables for a new round of fixedpoint computations
            failingPreAndPostConditions = mgr.constantFalse();
            T::execute();
            if (!realizable) {
                extractPatternsFromWinningStates();
            }
            iter++;
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysAfter.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvAfter.dot");

        // Mark states for which the counterstrategy has post inputs that are NOT winning for player 1, and enumerate those inputs.
        //   TODO: can do this post input quantification for the deadlock case also?
        BF candidateAll = mgr.constantFalse();
        BF candidateGuarAll = mgr.constantFalse();
        if (!realizable) {
        // if (false){
            std::cerr << "adding liveness assumptions and re-synthesizing the counter-strategy\n";
            // BF_newDumpDot(*this,candidateWinningPreConditions,NULL,"/tmp/candidateWinningPreConditions.dot");
            int iter = 0;
            for (auto it = foundCutConditions.begin();it!=foundCutConditions.end();it++) {
                std::cerr << "major iter " << iter << " for index " << boost::get<0>(*it) << "\n";
                // BF newLivenessAssumptions = boost::get<1>(*it).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput).ExistAbstract(varCubePreInput);
                BF newLivenessAssumptions = boost::get<1>(*it).ExistAbstract(varCubePostOutput).ExistAbstract(varCubePreInput);
                
                std::stringstream fname;
                fname << "/tmp/newLivenessAssumptions" << iter << "p" << boost::get<0>(*it) << ".dot";
                BF_newDumpDot(*this,newLivenessAssumptions,NULL,fname.str());
                
                BF TODO = newLivenessAssumptions; 
                int idx = 0;
                while (!TODO.isFalse()) {
                    BF cutAssignment = determinize(TODO,preOutputVars);
                    cutAssignment = determinize(cutAssignment,postInputVars);
                    TODO &= !cutAssignment;
                    BF cutPre = cutAssignment.ExistAbstract(varCubePost);
                    BF cutPost = cutAssignment.ExistAbstract(varCubePre);
                    // BF candidate = cutPre.Implies(cutPost);
                    BF candidate = cutPre & !cutPost;
                    int OKtoAdd = true;
                    if (!((safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)).isFalse())){ // if the candidate satisfies the system transition
                        for (unsigned int i=0;i<livenessAssumptions.size();i++) {
                            if ((livenessAssumptions[i] & (!candidate)).isFalse()){ // if the new assumption is already in the list
                                // livenessAssumptions[i] &= candidate; //strengthen existing livenesses if needed, but don't append
                                OKtoAdd = false;
                                std::cerr << "didn't add a candidate assumption in " << boost::get<0>(*it) << ". It was redundant with liveness " << i << "\n";
                                break;
                            }
                            // if ((livenessAssumptions[i] & candidate).isFalse()){ // if the new assumption may falsfy the env
                            //     OKtoAdd = false;
                            //     break;
                            // }

                            // std::stringstream fname;
                            // fname << "/tmp/livenessAssumptions" << iter << "i" << i << ".dot";
                            // BF_newDumpDot(*this,livenessAssumptions[i],NULL,fname.str());
                        }
                    }
                    else {OKtoAdd = false;}
                    // std::stringstream fname;
                    // fname << "/tmp/newLivenessAssumptionsFalseSys" << boost::get<0>(*it) << ".dot";
                    // BF_newDumpDot(*this,(safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)),NULL,fname.str());    
                    if (OKtoAdd){
                        // livenessAssumptions.push_back(candidate);
                        candidateAll |= candidate;
                        candidateGuarAll |= cutPre;
                        std::stringstream fname;
                        fname << "/tmp/addedLivenessAssumptions" << iter << "p" << boost::get<0>(*it) << "index" << idx << ".dot";
                        BF_newDumpDot(*this,candidate,NULL,fname.str());      
                    }
                    idx++;
                }
                // std::cerr << boost::get<0>(*it) << "\n";
                iter++;
            }
            livenessAssumptions.push_back(candidateAll); 
            livenessGuarantees.push_back(candidateGuarAll);
            // BF_newDumpDot(*this,livenessAssumptions.back(),NULL,"/tmp/livenessAssumptionsLast.dot");

            T::execute();
            if (!realizable) {
                extractPatternsFromWinningStates();
            }
        }   
        // livenessAssumptions.push_back(candidateWinningPreConditions);

        // check realizability; extract a strategy
        checkRealizabilityPlayer2();
        if (realizable) {
            std::cerr << "RESULT: Specification is realizable.\n";
            if (outputFilenameStrategy=="") {
                computeAndPrintExplicitStateStrategyPlayer2(std::cout);
            } else {
                std::ofstream of2(outputFilenameStrategy.c_str());
                computeAndPrintExplicitStateStrategyPlayer2(of2);
                of2.close();
            }
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }

    }

    void extractPatternsFromWinningStates() {

        failingPreAndPostConditions = mgr.constantFalse();
        foundCutConditions.clear();

        // We don't want any reordering from this point onwards, as
        // the BDD manipulations from this point onwards are 'kind of simple'.
        mgr.setAutomaticOptimisation(false);

        // List of states in existance so far. The first map
        // maps from a BF node pointer (for the pre variable valuation) and a goal
        // to a state number. The vector then contains the concrete valuation.
        std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > lookupTableForPastStates;
        std::vector<BF> bfsUsedInTheLookupTable;
        std::list<std::pair<size_t, std::pair<unsigned int, unsigned int> > > todoList;

        BF livelockCut = mgr.constantFalse();
        BF deadlockCut = mgr.constantTrue();
        
        // Prepare positional strategies for the individual goals
        std::vector<std::vector<BF> > positionalStrategiesForTheIndividualGoals(livenessAssumptions.size());
        for (unsigned int i=0;i<livenessAssumptions.size();i++) {
            //BF casesCovered = mgr.constantFalse();
            std::vector<BF> strategy(livenessGuarantees.size()+1);
            for (unsigned int j=0;j<livenessGuarantees.size()+1;j++) {
                strategy[j] = mgr.constantFalse();
            }
            for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
                if (boost::get<0>(*it) == i) {
                    //Have to cover each guarantee (since the winning strategy depends on which guarantee is being pursued)
                    //Essentially, the choice of which guarantee to pursue can be thought of as a system "move".
                    //The environment always to chooses that prevent the appropriate guarantee.
                    strategy[boost::get<1>(*it)] |= boost::get<2>(*it).UnivAbstract(varCubePostOutput) & !(strategy[boost::get<1>(*it)].ExistAbstract(varCubePost));
                }
            }
            positionalStrategiesForTheIndividualGoals[i] = strategy;
        }

        // Prepare initial to-do list from the allowed initial states. Select a single initial input valuation.

        // BF robotAllowedMoves = robotBDD.ExistAbstract(varCubePostMotionState);
        // TODO: Support for non-special-robotics semantics
        // failingPreAndPostConditions = winningPositions & safetyEnv & !safetySys;
        // failingPreAndPostConditions = robotAllowedMoves.Implies(failingPreAndPostConditions).ExistAbstract(varCubePostMotionState).UnivAbstract(varCubePostOutput).ExistAbstract(varCubePreInput);
        // failingPreAndPostConditions &= !(failingPreAndPostConditions.UnivAbstract(varCubePostInput)); // remove safeties that are pure obstacles.

        // BF_newDumpDot(*this,failingPreAndPostConditions,NULL,"/tmp/failingPreAndPostConditions.dot");

        // save any combination of pre variables and post inputs found that are not included in player 1's strategy and don't falsify the environment
        //TODO: for *all* post motion states? (by definition, any control output that is winning should produce motion states that are all winning)
        BF cutCandidate = safetyEnv & robotBDD & (!winningPositions.ExistAbstract(varCubePre)) & winningPositions.ExistAbstract(varCubePost);
        if (!cutCandidate.isFalse()) {
            foundCutConditions.push_back(boost::make_tuple(0,cutCandidate));
        }
    }

    void checkRealizabilityPlayer2() {

       // The greatest fixed point - called "Z" in the GR(1) synthesis paper
        BFFixedPoint nu2(mgr.constantTrue());

        // Iterate until we have found a fixed point
        for (;!nu2.isFixedPointReached();) {

            // To extract a strategy in case of realizability, we need to store a sequence of 'preferred' transitions in the
            // game structure. These preferred transitions only need to be computed during the last execution of the outermost
            // greatest fixed point. Since we don't know which one is the last one, we store them in every iteration,
            // so that after the last iteration, we obtained the necessary data. Before any new iteration, we need to
            // clear the old data, though.
            strategyDumpingData.clear();

            // Iterate over all of the liveness guarantees. Put the results into the variable 'nextContraintsForGoals' for every
            // goal. Then, after we have iterated over the goals, we can update nu2.
            BF nextContraintsForGoals = mgr.constantTrue();
            for (unsigned int j=0;j<livenessGuarantees.size();j++) {

                // Start computing the transitions that lead closer to the goal and lead to a position that is not yet known to be losing.
                // Start with the ones that actually represent reaching the goal (which is a transition in this implementation as we can have
                // nexts in the goal descriptions).
                BF livetransitions = livenessGuarantees[j] & (nu2.getValue().SwapVariables(varVectorPre,varVectorPost));

                // Compute the middle least-fixed point (called 'Y' in the GR(1) paper)
                BFFixedPoint mu1(mgr.constantFalse());
                for (;!mu1.isFixedPointReached();) {

                    // Update the set of transitions that lead closer to the goal.
                    livetransitions |= mu1.getValue().SwapVariables(varVectorPre,varVectorPost);

                    // Iterate over the liveness assumptions. Store the positions that are found to be winning for *any*
                    // of them into the variable 'goodForAnyLivenessAssumption'.
                    BF goodForAnyLivenessAssumption = mu1.getValue();
                    for (unsigned int i=0;i<livenessAssumptions.size();i++) {

                        // Prepare the variable 'foundPaths' that contains the transitions that stay within the inner-most
                        // greatest fixed point or get closer to the goal. Only used for strategy extraction
                        BF foundPaths = mgr.constantTrue();

                        // Inner-most greatest fixed point. The corresponding variable in the paper would be 'X'.
                        BFFixedPoint nu0(mgr.constantTrue());
                        for (;!nu0.isFixedPointReached();) {

                            // Compute a set of paths that are safe to take - used for the enforceable predecessor operator ('cox')
                            foundPaths = livetransitions | (nu0.getValue().SwapVariables(varVectorPre,varVectorPost) & !(livenessAssumptions[i]));
                            foundPaths &= safetySys;

                            // Update the inner-most fixed point with the result of applying the enforcable predecessor operator
                            nu0.update(safetyEnv.Implies(foundPaths).ExistAbstract(varCubePostOutput).UnivAbstract(varCubePostInput));
                        }

                        // Update the set of positions that are winning for some liveness assumption
                        goodForAnyLivenessAssumption |= nu0.getValue();

                        // Dump the paths that we just wound into 'strategyDumpingData' - store the current goal long
                        // with the BDD
                        strategyDumpingData.push_back(std::pair<unsigned int,BF>(j,foundPaths));
                    }

                    // Update the moddle fixed point
                    mu1.update(goodForAnyLivenessAssumption);
                }

                // Update the set of positions that are winning for any goal for the outermost fixed point
                nextContraintsForGoals &= mu1.getValue();
            }

            // Update the outer-most fixed point
            nu2.update(nextContraintsForGoals);

        }

        // We found the set of winning positions
        winningPositionsPlayer2 = nu2.getValue();
        BF_newDumpDot(*this,winningPositionsPlayer2,NULL,"/tmp/winningPositionsPlayer2.dot");

        // Check if for every possible environment initial position the system has a good system initial position
        // BF robotInit = robotBDD.ExistAbstract(varCubePost);
                // Check if for every possible environment initial position the system has a good system initial position
        BF result;
        if (initSpecialRoboticsSemantics) {
            result = (initEnv & initSys).Implies(winningPositionsPlayer2).UnivAbstract(varCubePreOutput).UnivAbstract(varCubePreInput);
        } else {
            result = initEnv.Implies(winningPositionsPlayer2 & initSys).ExistAbstract(varCubePreOutput).UnivAbstract(varCubePreInput);
        }
        // BF_newDumpDot(*this,(winningPositions & initSys),NULL,"/tmp/winningAndInit.dot");
        // BF_newDumpDot(*this,result,NULL,"/tmp/result.dot");

        // Check if the result is well-defind. Might fail after an incorrect modification of the above algorithm
        if (!result.isConstant()) throw "Internal error: Could not establish realizability/unrealizability of the specification.";

        // Return the result in Boolean form.
        realizable = result.isTrue();
    }

    void computeAndPrintExplicitStateStrategyPlayer2(std::ostream &outputStream) {

        // We don't want any reordering from this point onwards, as
        // the BDD manipulations from this point onwards are 'kind of simple'.
        mgr.setAutomaticOptimisation(false);

        // List of states in existance so far. The first map
        // maps from a BF node pointer (for the pre variable valuation) and a goal
        // to a state number. The vector then contains the concrete valuation.
        std::map<std::pair<size_t, unsigned int>, unsigned int > lookupTableForPastStates;
        std::vector<BF> bfsUsedInTheLookupTable;
        std::list<std::pair<size_t, unsigned int> > todoList;

        // Prepare initial to-do list from the allowed initial states
        BF todoInit = (oneStepRecovery)?(winningPositions & initSys):(winningPositions & initSys & initEnv);
        while (!(todoInit.isFalse())) {
            BF concreteState = determinize(todoInit,preVars);
            std::pair<size_t, unsigned int> lookup = std::pair<size_t, unsigned int>(concreteState.getHashCode(),0);
            lookupTableForPastStates[lookup] = bfsUsedInTheLookupTable.size();
            bfsUsedInTheLookupTable.push_back(concreteState);
            todoInit &= !concreteState;
            todoList.push_back(lookup);
        }

        // Prepare positional strategies for the individual goals
        std::vector<BF> positionalStrategiesForTheIndividualGoals(livenessGuarantees.size());
        for (unsigned int i=0;i<livenessGuarantees.size();i++) {
            BF casesCovered = mgr.constantFalse();
            BF strategy = mgr.constantFalse();
            for (auto it = strategyDumpingData.begin();it!=strategyDumpingData.end();it++) {
                if (it->first == i) {
                    BF newCases = it->second.ExistAbstract(varCubePostOutput) & !casesCovered;
                    strategy |= newCases & it->second;
                    casesCovered |= newCases;
                }
            }
            positionalStrategiesForTheIndividualGoals[i] = strategy;
            BF_newDumpDot(*this,strategy,"PreInput PreOutput PostInput PostOutput","/tmp/generalStrategy.dot");
        }

        // Extract strategy
        while (todoList.size()>0) {
            std::pair<size_t, unsigned int> current = todoList.front();
            todoList.pop_front();
            unsigned int stateNum = lookupTableForPastStates[current];
            BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

            /*{
                std::ostringstream filename;
                filename << "/tmp/state" << stateNum << ".dot";
                BF_newDumpDot(*this,currentPossibilities,"PreInput PreOutput PostInput PostOutput",filename.str());
            }*/

            // Print state information
            outputStream << "State " << stateNum << " with rank " << current.second << " -> <";
            bool first = true;
            for (unsigned int i=0;i<variables.size();i++) {
                if (doesVariableInheritType(i,Pre)) {
                    if (first) {
                        first = false;
                    } else {
                        outputStream << ", ";
                    }
                    outputStream << variableNames[i] << ":";
                    outputStream << (((currentPossibilities & variables[i]).isFalse())?"0":"1");
                }
            }

            outputStream << ">\n\tWith successors : ";
            first = true;

            // Compute successors for all variables that allow these
            currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second];
            BF remainingTransitions =
                    (oneStepRecovery)?
                    currentPossibilities:
                    (currentPossibilities & safetyEnv);

            // Switching goals
            while (!(remainingTransitions.isFalse())) {
                BF newCombination = determinize(remainingTransitions,postVars);

                // Jump as much forward  in the liveness guarantee list as possible ("stuttering avoidance")
                unsigned int nextLivenessGuarantee = current.second;
                bool firstTry = true;
                while (((nextLivenessGuarantee != current.second) || firstTry) && !((livenessGuarantees[nextLivenessGuarantee] & newCombination).isFalse())) {
                    nextLivenessGuarantee = (nextLivenessGuarantee + 1) % livenessGuarantees.size();
                    firstTry = false;
                }

                // Mark which input has been captured by this case
                BF inputCaptured = newCombination.ExistAbstract(varCubePostOutput);
                newCombination = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);
                remainingTransitions &= !inputCaptured;

                // Search for newCombination
                unsigned int tn;
                std::pair<size_t, unsigned int> target = std::pair<size_t, unsigned int>(newCombination.getHashCode(),nextLivenessGuarantee);
                if (lookupTableForPastStates.count(target)==0) {
                    tn = lookupTableForPastStates[target] = bfsUsedInTheLookupTable.size();
                    bfsUsedInTheLookupTable.push_back(newCombination);
                    todoList.push_back(target);
                } else {
                    tn = lookupTableForPastStates[target];
                }

                // Print
                if (first) {
                    first = false;
                } else {
                    outputStream << ", ";
                }
                outputStream << tn;
            }

            outputStream << "\n";
        }
    }

    static GR1Context* makeInstance(std::list<std::string> &filenames) {
        return new XRefineAssumptions<T>(filenames);
    }
};

#endif
