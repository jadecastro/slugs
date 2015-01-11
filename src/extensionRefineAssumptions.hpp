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
    bool oneStepRecovery = true;

    SlugsVectorOfVarBFs preInputVars{PreInput,this};
    SlugsVectorOfVarBFs postInputVars{PostInput,this};
    SlugsVectorOfVarBFs preOutputVars{PreOutput,this};
    
    BF failingPreAndPostConditions = mgr.constantFalse();
    // std::vector<boost::tuple<unsigned int,BF> > foundCutConditions;
    BF foundCutConditions = mgr.constantTrue(); 

    std::vector<unsigned int> varIdxDeadlockPre;
    std::vector<unsigned int> varIdxDeadlockPost;

    std::vector<BF> candidateCutConditionsArray;
    std::vector<BF> candidateCutConditionsArrayVisualOnly;

    BF safetyEnvBeforeAdditions;

public:

    XRefineAssumptions<T>(std::list<std::string> &filenames) : T(filenames) {
        if (filenames.size()==1) {
            outputFilenameStrategy = "";
        } else {
            outputFilenameStrategy = filenames.front();
            filenames.pop_front();
            std::cerr << "Will be saving to: " << outputFilenameStrategy << "\n";
        }
    }

    void execute() {

        int numRobots = 2;
        for (unsigned int robotNum=0;robotNum<numRobots;robotNum++) {
            std::stringstream deadlockVariableString;
            deadlockVariableString << "rob" << robotNum+1 << "_deadlock";  // Look for variables labeled "deadlock_1", "deadlock_2", etc.
            // std::cerr << " Looking for: " << deadlockVariableString.str() << "\n";
            for (unsigned int j=0;j<variables.size()/2;j++) {
                // std::cerr << "    in: " << variableNames[2*j] << " (pre) \n";
                // std::cerr << "    in: " << variableNames[2*j+1] << " (post) \n";
                if ( variableNames[2*j].compare(0,deadlockVariableString.str().size(),deadlockVariableString.str()) == 0 ) {
                    varIdxDeadlockPre.push_back(2*j);
                    // std::cerr << " Found variable: " << variableNames[2*j] << " at " << j << "\n";
                }
                if ( variableNames[2*j+1].compare(0,deadlockVariableString.str().size(),deadlockVariableString.str()) == 0 ) {
                    varIdxDeadlockPost.push_back(2*j+1);
                    // std::cerr << " Found variable: " << variableNames[2*j+1] << " at " << j << "\n";
                }
            }
        }

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

            if (!foundRevisions) {throw SlugsException(false,"Error: did not find any safety revisions!\n");}
            std::cerr << "\n";

            // std::cerr << "Deadlock revisions found.\nWhen within " << maxDist << " of station_1, never set environment variable s1_occupied to True.\nAccept? (y/n)";
            char userResponse = 'y';
            // std::cin >> userResponse;
            if (userResponse == 'y') {
                safetySys &= safetySysTent;
                safetyEnv &= safetyEnvTent;
            }

            // prepare the variables for a new round of fixed-point computations
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
        BF safetyEnvLast = mgr.constantTrue();

        safetyEnvBeforeAdditions = safetyEnv;

        while (!realizable) {
        // if (false){
            std::cerr << "adding liveness assumptions and re-synthesizing the counter-strategy\n";
            // BF_newDumpDot(*this,candidateWinningPreConditions,NULL,"/tmp/candidateWinningPreConditions.dot");

            // BF newLivenessAssumptions = boost::get<1>(*it).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput).ExistAbstract(varCubePreInput);
            BF newLivenessAssumptions = (foundCutConditions).ExistAbstract(varCubePostOutput);
            
            // BF_newDumpDot(*this,foundCutConditions,"PreInput PreOutput PostInput PostOutput","/tmp/foundCutConditions.dot");
            // BF_newDumpDot(*this,newLivenessAssumptions,"PreInput PreOutput PostInput PostOutput","/tmp/newLivenessAssumptions.dot");
            
            // BF todo = newLivenessAssumptions; 
            // int idx = 0;
            // while (!todo.isFalse()) {
            //     if ( idx % 500 == 0 ) {
            //         std::cerr << "   processing candidate index: " << idx << "\n";
            //     }
            //     BF cutAssignment = determinize(todo,preInputVars);
            //     cutAssignment = determinize(cutAssignment,preOutputVars);
            // //     cutAssignment = determinize(cutAssignment,postInputVars);
            //     todo &= !cutAssignment;
            //     BF cutPre = cutAssignment.ExistAbstract(varCubePost);
            //     BF cutPost = cutAssignment.ExistAbstract(varCubePre);
            // //     // BF candidate = cutPre.Implies(cutPost);
            //     BF candidate = safetyEnv & cutPre & !cutPost;
            //     BF candidateSafety = safetyEnv & (candidate.ExistAbstract(varCubePost)).Implies(!candidate.ExistAbstract(varCubePre));


            //     // candidateCutConditionsArray.push_back(candidateSafety);
            //     // candidateCutConditionsArrayVisualOnly.push_back(candidate);

            //     bool testIfChanging = false;
            //     for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
            //         BF testForTrueDeadlockPre = ( (cutAssignment & variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
            //         BF testForFalseDeadlockPre = ( (cutAssignment & !variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
            //         std::cerr << "   iteration: " << idx << " testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
            //         BF testForTrueDeadlockPost = ( (cutAssignment & variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
            //         BF testForFalseDeadlockPost = ( (cutAssignment & !variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
            //         std::cerr << "   iteration: " << idx << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";
                    
            //         // testIfChanging |= ( !testForTrueDeadlockPre.isFalse() & testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() ); // | ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
            //         testIfChanging |= ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
            //     }
            //     std::stringstream fname;
            //     fname << "/tmp/livenessCuts" << idx << ".dot";
            //     BF_newDumpDot(*this,candidate,"PreInput PreOutput PostInput PostOutput",fname.str());  

            //     std::stringstream fname1;
            //     fname1 << "/tmp/cutAssignment" << idx << ".dot";
            //     BF_newDumpDot(*this,cutAssignment,"PreInput PreOutput PostInput PostOutput",fname1.str());  

            //     if (testIfChanging) {
            //         candidateCutConditionsArray.push_back(candidateSafety);
            //         candidateCutConditionsArrayVisualOnly.push_back(candidate);
            //     }
            //     // int okToAdd = true;
            //     // if (!((safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)).isFalse())){ // if the candidate satisfies the system transition
            //     //     for (unsigned int i=0;i<livenessAssumptions.size();i++) {
            //     //         // if ((livenessAssumptions[i] & (!candidate)).isFalse()){ // if the new assumption is already in the list
            //     //         //     // livenessAssumptions[i] &= candidate; //strengthen existing livenesses if needed, but don't append
            //     //         //     okToAdd = false;
            //     //         //     std::cerr << "didn't add candidate assumption. It was redundant with liveness " << i << "\n";
            //     //         //     break;
            //     //         // }
            //     //         if ((livenessAssumptions[i] & candidate).isFalse()){ // if the new assumption may falsfy the env
            //     //             okToAdd = false;
            //     //             break;
            //     //         }

            //     //         // std::stringstream fname;
            //     //         // fname << "/tmp/livenessAssumptions" << iter << "i" << i << ".dot";
            //     //         // BF_newDumpDot(*this,livenessAssumptions[i],NULL,fname.str());
            //     //     }
            //     // }
            //     // else {okToAdd = false;}

            //     // // std::stringstream fname;
            //     // // fname << "/tmp/newLivenessAssumptionsFalseSys" << boost::get<0>(*it) << ".dot";
            //     // // BF_newDumpDot(*this,(safetySys & candidate.SwapVariables(varVectorPre,varVectorPost)),NULL,fname.str());    
            //     // if (okToAdd){
            //     //     // livenessAssumptions.push_back(candidate);
            //     //     candidateAll |= candidate;
            //     //     // candidateGuarAll |= cutPre;
                    
            //     //     // std::stringstream fname;
            //     //     // fname << "/tmp/addedLivenessAssumptions" << idx << ".dot";
            //     //     // BF_newDumpDot(*this,candidate,NULL,fname.str());      
            //     // }
            //     idx++;
            // }

            // BF_newDumpDot(*this,candidateAll,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAll.dot");
            // if (!newLivenessAssumptions.isFalse()) {
                std::cerr << "Adding the found conditions...\n";
                // livenessAssumptions.push_back(candidateAll); 
                // livenessAssumptions[0] = livenessAssumptions[0] & candidateAll;
                // livenessGuarantees.push_back(candidateGuarAll);
                BF_newDumpDot(*this,livenessAssumptions.front(),"PreInput PreOutput PostInput PostOutput","/tmp/livenessAssumptionsFirst.dot");
                BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvBEFORE.dot");
                // Check cut assignment candidates one by one. Iterate until we get one that renders the specification realizable.   
                //    Note: assuming here that we are aiming to modify the first entry. 
                // BF tmpLivenessAssumptions = livenessAssumptions[0];
                // BF tmpSafetyEnv = safetyEnv;
                for (unsigned int i=0;i<candidateCutConditionsArray.size();i++) {
                    std::cerr << "  iteration " << i << "\n";
                    // bool testIfChanging = false;
                    // for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
                    //     BF testForTrueDeadlockPre = ( (candidateCutConditionsArrayVisualOnly[i] & variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    //     BF testForFalseDeadlockPre = ( (candidateCutConditionsArrayVisualOnly[i] & !variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    //     // std::cerr << "     testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
                    //     BF testForTrueDeadlockPost = ( (candidateCutConditionsArrayVisualOnly[i] & variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    //     BF testForFalseDeadlockPost = ( (candidateCutConditionsArrayVisualOnly[i] & !variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    //     // std::cerr << "     testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";
                        
                    //     // testIfChanging |= ( !testForTrueDeadlockPre.isFalse() & testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() ); // | ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
                    //     testIfChanging |= ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
                    // }
                    // candidate fits the pattern if there is a change in the deadlock status
                    if ( (!(safetyEnv & candidateCutConditionsArray[i]).isFalse())) {
                        // std::cerr << "  iteration " << i << "\n";
                        // livenessAssumptions[0] &= candidateCutConditionsArray[i];
                        safetyEnv &= candidateCutConditionsArray[i];

                        // T::execute();

                        std::stringstream fname;
                        fname << "/tmp/newEnvSafety" << i << ".dot";
                        BF_newDumpDot(*this,candidateCutConditionsArray[i],"PreInput PreOutput PostInput PostOutput",fname.str());  
                        // BF_newDumpDot(*this,candidateCutConditionsArrayVisualOnly[i],"PreInput PreOutput PostInput PostOutput","/tmp/newEnvSafety.dot");
                        
                        // if (realizable) { 
                        //     //check if added liveness may be falsified by the system
                        //     std::cerr << "Testing the new assumptions...\n";
                            
                        //     livenessGuarantees.push_back(mgr.constantFalse());
                        //     checkRealizabilityPlayer2();
                        //     livenessGuarantees.pop_back();
                            
                        //     if (realizable) {
                        //         livenessAssumptions[0] = tmpLivenessAssumptions;
                        //         std::cerr << "Added assumptions falsify the environment!! \n";
                        //     } else {
                        //         std::cerr << "Success at iteration " << i << "\n";
                        //         BF_newDumpDot(*this,candidateCutConditionsArrayVisualOnly[i],"PreInput PreOutput PostInput PostOutput","/tmp/newEnvSafety.dot");
                        //         break;                             
                        //     }
                        // } else {
                        //     // livenessAssumptions[0] = tmpLivenessAssumptions;
                        //     // safetyEnv = tmpSafetyEnv;
                        // }
                    } else {
                        std::cerr << "  iteration " << i << " faslified the env\n";
                    }
                }
                // check whether or not we're doing anything
                if ((!safetyEnv & safetyEnvLast).isFalse()) {
                    throw SlugsException(false,"Error: did not find any new safety assumptions!\n");
                }
                safetyEnvLast = safetyEnv;
                BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvAFTER.dot");

                // break;
                candidateCutConditionsArray.clear();
                candidateCutConditionsArrayVisualOnly.clear();
                strategyDumpingData.clear();

                T::execute();
                if (!realizable) {
                    extractPatternsFromWinningStates();
                }
            // }
            // else {
            //     throw SlugsException(false,"Error: did not find any non-falsifying liveness cut conditions!\n");
            // }
        }
        // livenessAssumptions.push_back(candidateWinningPreConditions);

        //check if added liveness may be falsified by the system
        BF_newDumpDot(*this,livenessAssumptions[0],"PreInput PreOutput PostInput PostOutput","/tmp/newEnvLiveness.dot");
        std::cerr << "Testing the new liveness assumptions...\n";

        livenessGuarantees.push_back(mgr.constantFalse());
        checkRealizabilityPlayer2();
        livenessGuarantees.pop_back();
        if (realizable) {
            SlugsException ex(false);
            ex << "Added liveness assumptions falsify the environment!! \n";
            throw ex;
        }

        // check realizability; extract a strategy
        checkRealizabilityPlayer2();
        if (realizable) {
            std::cerr << "RESULT: Specification is realizable.\n";
            if (outputFilenameStrategy=="") {
                computeAndPrintExplicitStateStrategyPlayer2(std::cout);
            } else {
                std::ofstream of2(outputFilenameStrategy.c_str());
                if (of2.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Could not open output file'" << outputFilenameStrategy << "\n";
                    throw ex;
                }
                computeAndPrintExplicitStateStrategyPlayer2(of2);
                if (of2.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Writing to output file'" << outputFilenameStrategy << "failed. \n";
                    throw ex;
                }
                of2.close();
            }
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
        }

    }

    void extractPatternsFromWinningStates() {

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
            // BF casesCovered = mgr.constantFalse();
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
                    // BF newCases = boost::get<2>(*it) & !casesCovered;
                    // strategy[boost::get<1>(*it)] |= newCases & boost::get<2>(*it);
                    // casesCovered |= newCases;

                    std::stringstream fname;
                    fname << "/tmp/strategy" << i << "by" << boost::get<1>(*it) << ".dot";
                    BF_newDumpDot(*this,strategy[boost::get<1>(*it)],NULL,fname.str());
                }
            }
            positionalStrategiesForTheIndividualGoals[i] = strategy;
        }
        
        // Prepare initial to-do list from the allowed initial states. Select a single initial input valuation.

        // TODO: Support for non-special-robotics semantics
        BF todoInit = (winningPositions & initEnv & initSys);
        while (!(todoInit.isFalse())) {
            BF concreteState = determinize(todoInit,preVars);
            
            //find which liveness guarantee is being prevented (finds the first liveness in order specified)
            // Note by Ruediger here: Removed "!livenessGuarantees[j]" as condition as it is non-positional
            unsigned int found_j_index = 0;
            for (unsigned int j=0;j<livenessGuarantees.size();j++) {
                if (!(concreteState & positionalStrategiesForTheIndividualGoals[0][j]).isFalse()) {
                    found_j_index = j;
                    break;
                }
            }
                
            std::pair<size_t, std::pair<unsigned int, unsigned int> > lookup = std::pair<size_t, std::pair<unsigned int, unsigned int> >(concreteState.getHashCode(),std::pair<unsigned int, unsigned int>(0,found_j_index));
            lookupTableForPastStates[lookup] = bfsUsedInTheLookupTable.size();
            bfsUsedInTheLookupTable.push_back(concreteState);
            //from now on use the same initial input valuation (but consider all other initial output valuations)
            todoInit &= !concreteState;
            todoList.push_back(lookup);
        }

        // Extract strategy
        int iter = 0;
        while (todoList.size()>0) {
            std::pair<size_t, std::pair<unsigned int, unsigned int> > current = todoList.front();
            todoList.pop_front();
            unsigned int stateNum = lookupTableForPastStates[current];
            BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

            // Can we enforce a deadlock?
            BF deadlockInput = (currentPossibilities & safetyEnv & !safetySys).UnivAbstract(varCubePostOutput);
            if (deadlockInput!=mgr.constantFalse()) {
          addDeadlocked(deadlockInput, current, bfsUsedInTheLookupTable,  lookupTableForPastStates, deadlockCut);
            } else {

                // No deadlock in sight -> Jump to a different liveness guarantee if necessary.
                while ((currentPossibilities & positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second])==mgr.constantFalse()) current.second.second = (current.second.second + 1) % livenessGuarantees.size();
                currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second];
                assert(currentPossibilities != mgr.constantFalse());
                BF remainingTransitions = currentPossibilities;

                // save any combination of pre variables and post inputs found that are not included in player 1's strategy
                BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitions.dot");
                // std::stringstream fname1;
                // fname1 << "/tmp/remainingTransitions" << iter << ".dot";
                // BF_newDumpDot(*this,remainingTransitions,"PreInput PreOutput PostInput PostOutput",fname1.str());  
            
                // add this transition to the set of possible edges to cut to prevent livelock for goal j.
                // removing any edge should allow the system to escape livelock.

                BF tmp = (safetyEnv & (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre))).ExistAbstract(varCubePostOutput);
                
                // std::cerr << "check for winning: " << tmp.isFalse() << "\n";
                // BF_newDumpDot(*this,(!remainingTransitions.ExistAbstract(varCubePre)),NULL,"/tmp/checkForWinning.dot");
                // BF_newDumpDot(*this,tmp,NULL,"/tmp/checkForWinningNotWinning.dot");
                
                // livelockCut |= (remainingTransitions);
                // livelockCut |= (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre)); // & (!winningPositions.SwapVariables(varVectorPre,varVectorPost)) );

                // BF_newDumpDot(*this,!(remainingTransitions).ExistAbstract(varCubePre),NULL,"/tmp/candidateWinningThisState.dot");
             //    std::stringstream ss1;
             //    std::stringstream ss2;
             //    ss1 << "/tmp/candidateWinning" << stateNum << ".dot";
             //    ss2 << "/tmp/remainingTransitions" << stateNum << ".dot";
             //    BF_newDumpDot(*this,(!remainingTransitions.ExistAbstract(varCubePre)) & remainingTransitions.ExistAbstract(varCubePost),NULL,ss1.str());
             //    BF_newDumpDot(*this,remainingTransitions,NULL,ss2.str());

                // Choose one next input and stick to it!
                // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsBefore.dot");
                remainingTransitions = determinize(remainingTransitions,postInputVars);
                // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsAfter.dot");

                // std::stringstream fname1;
                // fname1 << "/tmp/remainingTransitions" << iter << ".dot";
                // BF_newDumpDot(*this,remainingTransitions,"PreInput PreOutput PostInput PostOutput",fname1.str());  

                bool testIfChanging = false;
                for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
                    BF testForTrueDeadlockPre = ( (remainingTransitions & variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    BF testForFalseDeadlockPre = ( (remainingTransitions & !variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    // std::cerr << "   iteration: " << iter << " testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
                    BF testForTrueDeadlockPost = ( (remainingTransitions & variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    BF testForFalseDeadlockPost = ( (remainingTransitions & !variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    // std::cerr << "   iteration: " << iter << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";
                    
                    // testIfChanging |= ( !testForTrueDeadlockPre.isFalse() & testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() ); // | ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
                    testIfChanging |= ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
                }
                // std::stringstream fname;
                // fname << "/tmp/livenessCuts" << iter << ".dot";
                // BF_newDumpDot(*this,(safetyEnv & (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre))),"PreInput PreOutput PostInput PostOutput",fname.str());  

                if (testIfChanging) {
                    std::cerr << "   iteration: " << iter << " to be cut.\n";
                    std::stringstream fname;
                    fname << "/tmp/livenessCuts" << iter << ".dot";
                    BF_newDumpDot(*this,(remainingTransitions.ExistAbstract(varCubePost)).Implies(!remainingTransitions.ExistAbstract(varCubePre)),"PreInput PreOutput PostInput PostOutput",fname.str());  
                    candidateCutConditionsArray.push_back(((remainingTransitions.ExistAbstract(varCubePost)).Implies(!remainingTransitions.ExistAbstract(varCubePre))));
                    candidateCutConditionsArrayVisualOnly.push_back(tmp);
                }

                // Switching goals
                while (!(remainingTransitions & safetySys).isFalse()) {

              
                    BF safeTransition = remainingTransitions & safetySys;
                    BF newCombination = determinize(safeTransition, postOutputVars);

                      
                    // Jump as much forward  in the liveness assumption list as possible ("stuttering avoidance")
                    unsigned int nextLivenessAssumption = current.second.first;
                    bool firstTry = true;
                    while (((nextLivenessAssumption != current.second.first) | firstTry) && !((livenessAssumptions[nextLivenessAssumption] & newCombination).isFalse())) {
                        nextLivenessAssumption  = (nextLivenessAssumption + 1) % livenessAssumptions.size();
                        firstTry = false;
                    }

                    //Mark which input has been captured by this case. Use the same input for other successors
                    remainingTransitions &= !newCombination;

                    // We don't need the pre information from the point onwards anymore.
                    newCombination = newCombination.ExistAbstract(varCubePre).SwapVariables(varVectorPre,varVectorPost);

                    unsigned int tn;

                    std::pair<size_t, std::pair<unsigned int, unsigned int> > target;

                    target = std::pair<size_t, std::pair<unsigned int, unsigned int> >(newCombination.getHashCode(),std::pair<unsigned int, unsigned int>(nextLivenessAssumption, current.second.second));

                    if (lookupTableForPastStates.count(target)==0) {
                        tn = lookupTableForPastStates[target] = bfsUsedInTheLookupTable.size();
                        bfsUsedInTheLookupTable.push_back(newCombination);
                        todoList.push_back(target);
                    } else {
                        tn = lookupTableForPastStates[target];
                    }

                }
            }
            iter++;
        }

        // need to cut the counterstrategy for each goal
        if (livelockCut.isFalse()) {
        foundCutConditions = deadlockCut;
        }   else {
            foundCutConditions = livelockCut;
        }
          
        
    }


        //This function adds a new successor-less "state" that captures the deadlock-causing input values
        //The outputvalues are omitted (indeed, no valuation exists that satisfies the system safeties)
        //Format compatible with JTLV counterstrategy

      void addDeadlocked(BF targetPositionCandidateSet, std::pair<size_t, std::pair<unsigned int, unsigned int> > current, std::vector<BF> &bfsUsedInTheLookupTable, std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > &lookupTableForPastStates, BF &deadlockCut) {
        
        BF newCombination = determinize(targetPositionCandidateSet, postVars) ;
        
        newCombination  = (newCombination.ExistAbstract(varCubePostOutput).ExistAbstract(varCubePre)).SwapVariables(varVectorPre,varVectorPost);

        unsigned int stateNum = lookupTableForPastStates[current];
        BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

        //cut to exclude current transition from counterstrategy
        deadlockCut &= currentPossibilities.Implies(!newCombination.SwapVariables(varVectorPost,varVectorPre));
        // deadlockCut &= (currentPossibilities.ExistAbstract(varCubePost)).Implies(!newCombination.SwapVariables(varVectorPre,varVectorPost).ExistAbstract(varCubePre).ExistAbstract(varCubePostOutput)); 
        
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
            strategyDumpingDataPlayer2.clear();

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
                        strategyDumpingDataPlayer2.push_back(std::pair<unsigned int,BF>(j,foundPaths));
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
        // BF todoInit = (oneStepRecovery)?(winningPositionsPlayer2 & initSys):(winningPositionsPlayer2 & initSys & initEnv);
        BF todoInit = (winningPositionsPlayer2 & initSys & initEnv);
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
            for (auto it = strategyDumpingDataPlayer2.begin();it!=strategyDumpingDataPlayer2.end();it++) {
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
                    (currentPossibilities & safetyEnvBeforeAdditions):
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
