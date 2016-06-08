#ifndef FINDREVISIONS_H
#define FINDREVISIONS_H


#include "gr1context.hpp"
#include <map>
#include <string>


template<class T1, class T2, class T3> class XFindRevisions : public T1, public T2, public T3 {
protected:

    // New variables
    std::string outputFilenameStrategy;

    // Inherit stuff that we actually use here.
    using T1::realizable;
    using T1::variables;
    using T1::variableTypes;
    using T1::variableNames;
    using T1::checkRealizability;
    using T1::determinize;
    using T1::doesVariableInheritType;
    using T1::mgr;
    using T1::varCubePre;
    using T1::varCubePost;
    using T1::varCubePostInput;
    using T1::varCubePostOutput;
    using T1::varCubePreInput;
    using T1::varCubePreOutput;
    using T1::preVars;
    using T1::postVars;
    using T1::postOutputVars;
    using T1::livenessAssumptions;
    using T1::livenessGuarantees;
    using T1::safetyEnv;
    using T1::safetySys;
    using T1::initEnv;
    using T1::initSys;
    using T1::varVectorPre;
    using T1::varVectorPost;
    using T1::strategyDumpingData;
    using T1::winningPositions;

    using T2::strategyDumpingData = strategyDumpingDataPlayer2;

    BF winningPositionsPlayer2;
    bool initSpecialRoboticsSemantics = false;
    bool oneStepRecovery = true;
    bool saveCounterstrategy = true;
    bool userFeedbackFlag = true;

    SlugsVectorOfVarBFs preInputVars{PreInput,this};
    SlugsVectorOfVarBFs postInputVars{PostInput,this};
    SlugsVectorOfVarBFs preOutputVars{PreOutput,this};

    BF failingPreAndPostConditions = mgr.constantFalse();
    // std::vector<boost::tuple<unsigned int,BF> > foundCutConditions;
    BF foundCutConditions = mgr.constantTrue();

    std::vector<unsigned int> varIdxDeadlockPre;
    std::vector<unsigned int> varIdxDeadlockPost;
    std::vector<unsigned int> varIdxDeadlockMemory;
    std::vector<unsigned int> varIdxRobot1Pre;
    std::vector<unsigned int> varIdxRobot2Pre;
    std::vector<unsigned int> deadlockVariableVector;

    std::vector<BF> candidateCutConditionsArray;
    std::vector<BF> candidateCutConditionsArrayVisualOnly;
    std::vector<BF> candidateCutConditionsArrayStrongRestriction;
    std::vector<BF> candidateCutConditionsArrayStrongRestrictionVisualOnly;

    BF safetyEnvBeforeAdditions;
    BF candidateCutConditionsPlayer2;

public:

    XFindRevisions<T1, T2, T3>(std::list<std::string> &filenames) : T1(filenames) {
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
        // singleton
        for (unsigned int robotNum=0;robotNum<numRobots;robotNum++) {
            std::stringstream deadlockVariableString;
            deadlockVariableString << "rob" << robotNum+1 << "_deadlock";  // Look for variables labeled "deadlock_1", "deadlock_2", etc.
            deadlockVariableVector.push_back(robotNum+1);
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
        // pairwise
        for (unsigned int robotI=0;robotI<numRobots-1;robotI++) {
            for (unsigned int robotJ=robotI+1;robotJ<numRobots;robotJ++) {
                std::stringstream deadlockVariableString;
                deadlockVariableString << "rob" << robotI+1 << robotJ+1 << "_deadlock";
                deadlockVariableVector.push_back(10*(robotI+1)+robotJ+1);
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
        }
        // memory propositions
        int numDeadlockMemPropsPerRobot = 2;
        for (unsigned int deadlockMemNum=0;deadlockMemNum<numDeadlockMemPropsPerRobot;deadlockMemNum++) {
            for (unsigned int robotNum=0;robotNum<numRobots;robotNum++) {
                std::stringstream deadlockVariableString;
                deadlockVariableString << "m_rob" << robotNum+1 << "_deadlock" << deadlockMemNum+1;  // Look for variables labeled "deadlock_1", "deadlock_2", etc.
                // std::cerr << " Looking for: " << deadlockVariableString.str() << "\n";
                for (unsigned int j=0;j<variables.size()/2;j++) {
                    // std::cerr << "    in: " << variableNames[2*j] << " (pre) \n";
                    // std::cerr << "    in: " << variableNames[2*j+1] << " (post) \n";
                    if ( variableNames[2*j].compare(0,deadlockVariableString.str().size(),deadlockVariableString.str()) == 0 ) {
                        varIdxDeadlockMemory.push_back(2*j);
                        // std::cerr << " Found variable: " << variableNames[2*j] << " at " << j << "\n";
                    }
                    if ( variableNames[2*j+1].compare(0,deadlockVariableString.str().size(),deadlockVariableString.str()) == 0 ) {
                        varIdxDeadlockMemory.push_back(2*j+1);
                        // std::cerr << " Found variable: " << variableNames[2*j+1] << " at " << j << "\n";
                    }
                }
            }
        }

        std::stringstream robotVariableString;
        robotVariableString << "rob1_";
        for (unsigned int j=0;j<variables.size()/2;j++) {
            if ( variableNames[2*j].compare(0,robotVariableString.str().size(),robotVariableString.str()) == 0 ) {
                varIdxRobot1Pre.push_back(2*j);
                // std::cerr << " Found variable: " << variableNames[2*j] << " at " << j << "\n";
            }
        }
        std::stringstream robotVariableString1;
        robotVariableString1 << "rob2_";
        for (unsigned int j=0;j<variables.size()/2;j++) {
            if ( variableNames[2*j].compare(0,robotVariableString1.str().size(),robotVariableString1.str()) == 0 ) {
                varIdxRobot2Pre.push_back(2*j);
                // std::cerr << " Found variable: " << variableNames[2*j] << " at " << j << "\n";
            }
        }

        T::execute();
        if (!realizable) {
            std::ofstream of2(outputFilenameStrategy.c_str());
            extractPatternsFromWinningStates(of2);
            of2.close();
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysBefore.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvBefore.dot");

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
                std::ofstream of2(outputFilenameStrategy.c_str());
                extractPatternsFromWinningStates(of2);
                of2.close();
            }
            iter++;
        }

        BF_newDumpDot(*this,safetySys,NULL,"/tmp/safetySysAfter.dot");
        BF_newDumpDot(*this,safetyEnv,NULL,"/tmp/safetyEnvAfter.dot");

        // Mark states for which the counterstrategy has post inputs that are NOT winning for player 1, and enumerate those inputs.
        //   TODO: can do this post input quantification for the deadlock case also?
        BF candidateAll = mgr.constantTrue();
        BF candidateAllRobot2 = mgr.constantFalse();
        BF candidateAllRobot1 = mgr.constantFalse();
        BF candidateCheck = mgr.constantFalse();
        BF candidateCheckVisual = mgr.constantFalse();
        BF candidateGuarAll = mgr.constantFalse();
        BF safetyEnvLast = mgr.constantTrue();

        safetyEnvBeforeAdditions = safetyEnv;

        while (!realizable) {
        // if (false){
            std::cerr << "adding liveness assumptions and re-synthesizing the counter-strategy\n";
            // BF_newDumpDot(*this,candidateWinningPreConditions,NULL,"/tmp/candidateWinningPreConditions.dot");

            // BF newLivenessAssumptions = boost::get<1>(*it).ExistAbstract(varCubePostMotionState).ExistAbstract(varCubePostControllerOutput).ExistAbstract(varCubePreInput);
            BF newLivenessAssumptions = (foundCutConditions).ExistAbstract(varCubePostOutput);

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
                if (candidateCutConditionsArray.size() == 0) {
                    candidateCutConditionsArray = candidateCutConditionsArrayStrongRestriction;
                    candidateCutConditionsArrayVisualOnly = candidateCutConditionsArrayStrongRestrictionVisualOnly;
                }
                for (unsigned int i=0;i<candidateCutConditionsArray.size();i++) {
                    std::cerr << "  Condition " << i << ":\n";

                    if ( (!(safetyEnv & candidateCutConditionsArray[i]).isFalse())) {
                        // std::cerr << "  iteration " << i << "\n";
                        // livenessAssumptions[0] &= candidateCutConditionsArray[i];
                        safetyEnv &= candidateCutConditionsArray[i];
                        candidateAll &= candidateCutConditionsArray[i];

                        BF tmp1 = candidateCutConditionsArrayVisualOnly[i];
                        for (unsigned int j=0;j<varIdxRobot1Pre.size();j++) {
                            tmp1 = tmp1.ExistAbstractSingleVar(variables[varIdxRobot1Pre[j]]);
                        }
                        candidateAllRobot2 |= tmp1;
                        BF tmp2 = candidateCutConditionsArrayVisualOnly[i];
                        for (unsigned int j=0;j<varIdxRobot2Pre.size();j++) {
                            tmp2 = tmp2.ExistAbstractSingleVar(variables[varIdxRobot2Pre[j]]);
                        }
                        candidateAllRobot1 |= tmp2;

                        // BF_newDumpDot(*this,candidateAllRobot1,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAllRobot1.dot");
                        // BF_newDumpDot(*this,candidateAllRobot2,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAllRobot2.dot");

                        BF tmp3 = candidateCutConditionsArrayVisualOnly[i];

                        for (unsigned int j=0;j<variables.size()/2;j++) {
                            // for (unsigned int j1=0;j1<varIdxDeadlockPre.size();j1++) {
                            //     std::cerr << "    Now on " << variableNames[varIdxDeadlockPre[j1]] << "\n";
                            if ((varIdxDeadlockPost[0] != 2*j+1) & (varIdxDeadlockPost[1] != 2*j+1)) {
                                // std::cerr << "     looking for post variable " << varIdxDeadlockPost[0] << "  " << 2*j+1 << "\n";
                                // std::cerr << "     abstracting pre variable " << variableNames[2*j+1] << "\n";
                                tmp3 = tmp3.ExistAbstractSingleVar(variables[2*j+1]);
                            }
                            // else{
                                // std::cerr << "     not abstacting " << variableNames[varIdxDeadlockPost[2*j+1]] << "\n";
                            // }
                            // }
                        }
                        BF_newDumpDot(*this,tmp3,"PreInput PreOutput PostInput PostOutput","/tmp/candidateCheckSingleCase.dot");
                        tmp3 = ((safetyEnv & tmp3.ExistAbstract(varCubePost)).Implies(!tmp3.ExistAbstract(varCubePre))).ExistAbstract(varCubePostOutput);
                        // tmp3 = tmp3.ExistAbstract(varCubePost) & (!tmp3).ExistAbstract(varCubePre);
                        BF_newDumpDot(*this,candidateCutConditionsArrayVisualOnly[i],"PreInput PreOutput PostInput PostOutput","/tmp/candidateCutConditionsArrayVisualOnly.dot");
                        // BF_newDumpDot(*this,tmp3,"PreInput PreOutput PostInput PostOutput","/tmp/candidateCheckSingleCase.dot");
                        candidateCheckVisual |= candidateCutConditionsArrayVisualOnly[i];

                        // Display the single-assignment to the user in sentence form
                        if (userFeedbackFlag){
                            std::stringstream userFeedback;
                            bool firstStatement = true;
                            userFeedback << "The environment should not cause ";
                            for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
                                BF testForTrueDeadlockPost = ( (candidateCutConditionsArrayVisualOnly[i] & variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                                BF testForFalseDeadlockPost = ( (candidateCutConditionsArrayVisualOnly[i] & !variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                                // std::cerr << "   iteration: " << iter << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";

                                if (!testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse()){
                                    if (firstStatement) {
                                        userFeedback << variableNames[varIdxDeadlockPre[j]];
                                        firstStatement = false;
                                    } else {
                                        userFeedback << " and " << variableNames[varIdxDeadlockPre[j]];
                                    }
                                }
                            }
                            userFeedback << " if ";
                            firstStatement = true;
                            for (unsigned int j=0;j<variables.size()/2;j++) {
                                BF testForTruePre = ( (candidateCutConditionsArrayVisualOnly[i] & variables[2*j]).ExistAbstractSingleVar(variables[2*j]) );
                                // std::cerr << "   iteration: " << iter << " testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
                                BF testForFalsePre = ( (candidateCutConditionsArrayVisualOnly[i] & !variables[2*j]).ExistAbstractSingleVar(variables[2*j]) );
                                // std::cerr << "   iteration: " << iter << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";

                                bool testAntecedant = !testForTruePre.isFalse() & testForFalsePre.isFalse();
                                if (testAntecedant){
                                    if (firstStatement) {
                                        userFeedback << variableNames[2*j];
                                        firstStatement = false;
                                    } else {
                                        userFeedback << " and " << variableNames[2*j];
                                    }
                                }
                            }
                            userFeedback << " are true in the current step and ";
                            firstStatement = true;
                            for (unsigned int j=0;j<variables.size()/2;j++) {
                                BF testForTruePost = ( (candidateCutConditionsArrayVisualOnly[i] & variables[2*j+1]).ExistAbstractSingleVar(variables[2*j+1]) );
                                // std::cerr << "   iteration: " << iter << " testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
                                BF testForFalsePost = ( (candidateCutConditionsArrayVisualOnly[i] & !variables[2*j+1]).ExistAbstractSingleVar(variables[2*j+1]) );
                                // std::cerr << "   iteration: " << iter << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";

                                bool testAntecedant = !testForTruePost.isFalse() & testForFalsePost.isFalse();
                                for (unsigned int j1=0;j1<varIdxDeadlockPost.size();j1++) {
                                    if (varIdxDeadlockPost[j1] == 2*j+1) {
                                        testAntecedant = false;
                                    }
                                }
                                if (testAntecedant){
                                    if (firstStatement) {
                                        userFeedback << variableNames[2*j];
                                        firstStatement = false;
                                    } else {
                                        userFeedback << " and " << variableNames[2*j];
                                    }
                                }
                            }
                            userFeedback << " are true in the next step.\n";
                            std::cerr << userFeedback.str();
                        }
                    } else {
                        std::cerr << "  iteration " << i << " faslified the env\n";
                    }
                }
                // check whether or not we're doing anything
                if ((!safetyEnv & safetyEnvLast).isFalse()) {
                    checkRealizabilityPlayer2();
                    if (realizable) {
                        std::cerr << "RESULT: Specification is realizable.\n";
                    }
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
                    std::ofstream of2(outputFilenameStrategy.c_str());
                    extractPatternsFromWinningStates(of2);
                    of2.close();
                }
            // }
            // else {
            //     throw SlugsException(false,"Error: did not find any non-falsifying liveness cut conditions!\n");
            // }
        }
        // livenessAssumptions.push_back(candidateWinningPreConditions);
        // BF_newDumpDot(*this,candidateAll,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAll.dot");
        BF_newDumpDot(*this,candidateCheckVisual.ExistAbstract(varCubePreInput),"PreInput PreOutput PostInput PostOutput","/tmp/candidateCheckVisual.dot");
        BF_newDumpDot(*this,candidateAllRobot1,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAllRobot1.dot");
        BF_newDumpDot(*this,candidateAllRobot2,"PreInput PreOutput PostInput PostOutput","/tmp/candidateAllRobot2.dot");

        //check if added liveness may be falsified by the system
        BF_newDumpDot(*this,livenessAssumptions[0],"PreInput PreOutput PostInput PostOutput","/tmp/newEnvLiveness.dot");
        std::cerr << "Testing the new environment assumptions...\n";

        if ((safetyEnv).isFalse()) {
            SlugsException ex(false);
            ex << "Added environment assumptions falsify the environment safety assumptions!! \n";
            throw ex;
        }

        livenessGuarantees.push_back(mgr.constantFalse());
        checkRealizabilityPlayer2();
        livenessGuarantees.pop_back();
        std::cerr << realizable << "\n";
        if (realizable) {
            SlugsException ex(false);
            ex << "Added environment assumptions falsify the environment!! \n";
            throw ex;
        }

        // check realizability; extract a strategy
        checkRealizabilityPlayer2();

        bool compareWithAndWithoutRecovery = true;

        if (realizable) {
            std::cerr << "RESULT: Specification is realizable.\n";
            if (outputFilenameStrategy=="") {
                if (compareWithAndWithoutRecovery) {
                    // oneStepRecovery = false;
                    candidateCutConditionsPlayer2 = mgr.constantFalse();
                    computeAndPrintExplicitStateStrategyPlayer2(std::cout,false);
                    BF winningNoRecovery = candidateCutConditionsPlayer2;
                    // oneStepRecovery = true;
                    candidateCutConditionsPlayer2 = mgr.constantFalse();
                    computeAndPrintExplicitStateStrategyPlayer2(std::cout,oneStepRecovery);
                    BF_newDumpDot(*this,(candidateCutConditionsPlayer2 & !winningNoRecovery),"PreInput PreOutput PostInput PostOutput","/tmp/recoverableTransitions.dot");
                }
            } else {
                std::ofstream of2(outputFilenameStrategy.c_str());
                if (of2.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Could not open output file'" << outputFilenameStrategy << "\n";
                    throw ex;
                }
                if (compareWithAndWithoutRecovery) {
                    // oneStepRecovery = false;
                    candidateCutConditionsPlayer2 = mgr.constantFalse();
                    computeAndPrintExplicitStateStrategyPlayer2(of2,false);
                    BF winningNoRecovery = candidateCutConditionsPlayer2;
                    of2.close();
                    std::ofstream of2(outputFilenameStrategy.c_str());
                    // oneStepRecovery = true;
                    candidateCutConditionsPlayer2 = mgr.constantFalse();
                    computeAndPrintExplicitStateStrategyPlayer2(of2,oneStepRecovery);
                    BF_newDumpDot(*this,(candidateCutConditionsPlayer2 & !winningNoRecovery),"PreInput PreOutput PostInput PostOutput","/tmp/recoverableTransitions.dot");
                    BF tmp = (candidateCutConditionsPlayer2 & !winningNoRecovery).ExistAbstract(varCubePost);
                    for (unsigned int j=0;j<varIdxRobot1Pre.size();j++) {
                        tmp = tmp.ExistAbstractSingleVar(variables[varIdxRobot1Pre[j]]);
                    }
                    BF_newDumpDot(*this,tmp,"PreInput PreOutput PostInput PostOutput","/tmp/recoverableTransitionsRobot2.dot");
                    tmp = (candidateCutConditionsPlayer2 & !winningNoRecovery).ExistAbstract(varCubePost);
                    for (unsigned int j=0;j<varIdxRobot2Pre.size();j++) {
                        tmp = tmp.ExistAbstractSingleVar(variables[varIdxRobot2Pre[j]]);
                    }
                    BF_newDumpDot(*this,tmp,"PreInput PreOutput PostInput PostOutput","/tmp/recoverableTransitionsRobot1.dot");
                }
                if (of2.fail()) {
                    SlugsException ex(false);
                    ex << "Error: Writing to output file'" << outputFilenameStrategy << "failed. \n";
                    throw ex;
                }
                of2.close();
            }
        } else {
            std::cerr << "RESULT: Specification is unrealizable.\n";
            // std::cerr << " Computing and saving the counterstrategy.... " << "\n";
            // if (!realizable) {
            //     if (outputFilenameStrategy=="") {
            //         computeAndPrintExplicitStateStrategy(std::cout);
            //     } else {
            //         std::stringstream nameStr
            //         outputFilenameCtr = outputFilenameStrategy.c_str() << 'ctr'
            //         std::ofstream of(outputFilenameCtr);
            //         std::cerr << "Will be saving counterstrategy to: " << outputFilenameCtr << "\n";
            //         if (of.fail()) {
            //             SlugsException ex(false);
            //             ex << "Error: Could not open output file'" << outputFilenameCtr << "\n";
            //             throw ex;
            //         }
            //         computeAndPrintExplicitStateStrategy(of);
            //         if (of.fail()) {
            //             SlugsException ex(false);
            //             ex << "Error: Writing to output file'" << outputFilenameCtr << "failed. \n";
            //             throw ex;
            //         }
            //         of.close();
            //     }
            // }
        }

    }

    void extractPatternsFromWinningStates(std::ostream &outputStream) {

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
        int numFound = 0;
        // while (numFound<1) {
            // std::cerr << "    numFound: " << numFound;
        while (todoList.size()>0) {
            std::pair<size_t, std::pair<unsigned int, unsigned int> > current = todoList.front();
            todoList.pop_front();
            unsigned int stateNum = lookupTableForPastStates[current];
            BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

            bool first = true;
            if (saveCounterstrategy) {
                // Print state information
                outputStream << "State " << stateNum << " with rank (" << current.second.first << "," << current.second.second << ") -> <";
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
            }

            // Can we enforce a deadlock?
            BF deadlockInput = (currentPossibilities & safetyEnv & !safetySys).UnivAbstract(varCubePostOutput);
            if (deadlockInput!=mgr.constantFalse()) {
          addDeadlocked(deadlockInput, current, bfsUsedInTheLookupTable,  lookupTableForPastStates, outputStream, deadlockCut);
            } else {

                // No deadlock in sight -> Jump to a different liveness guarantee if necessary.
                while ((currentPossibilities & positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second])==mgr.constantFalse()) current.second.second = (current.second.second + 1) % livenessGuarantees.size();
                currentPossibilities &= positionalStrategiesForTheIndividualGoals[current.second.first][current.second.second];
                assert(currentPossibilities != mgr.constantFalse());
                BF remainingTransitions = currentPossibilities;

                // save any combination of pre variables and post inputs found that are not included in player 1's strategy
                BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitions.dot");

                // add this transition to the set of possible edges to cut to prevent livelock for goal j.
                // removing any edge should allow the system to escape livelock.

                BF tmp = (safetyEnv & (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre))).ExistAbstract(varCubePostOutput);

                // livelockCut |= (remainingTransitions);
                // livelockCut |= (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre)); // & (!winningPositions.SwapVariables(varVectorPre,varVectorPost)) );

                // Choose one next input and stick to it!
                // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsBefore.dot");
                remainingTransitions = determinize(remainingTransitions,postInputVars);
                // BF_newDumpDot(*this,remainingTransitions,NULL,"/tmp/remainingTransitionsAfter.dot");

                BF tmp1 = (safetyEnv & (remainingTransitions.ExistAbstract(varCubePost)) & (!remainingTransitions.ExistAbstract(varCubePre))).ExistAbstract(varCubePostOutput);

                BF_newDumpDot(*this,tmp1,"PreInput PreOutput PostInput PostOutput","/tmp/tmp1.dot");
                // std::stringstream fname1;
                // fname1 << "/tmp/remainingTransitions" << iter << ".dot";
                // BF_newDumpDot(*this,remainingTransitions,"PreInput PreOutput PostInput PostOutput",fname1.str());

                std::vector<bool> testIfChanging;
                std::vector<bool> testIfChangingStrongRestriction;
                std::vector<BF> deadlockVarsChanging;
                std::vector<unsigned int> idxDeadlockRisingEdge;
                std::vector<unsigned int> idxDeadlockRisingEdgeStrongRestriction;
                for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
                    BF testForTrueDeadlockPre = ( (remainingTransitions & variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    BF testForFalseDeadlockPre = ( (remainingTransitions & !variables[varIdxDeadlockPre[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]) );
                    // std::cerr << "   iteration: " << iter << " testIfChangingPre: " << !testForTrueDeadlockPre.isFalse() << !testForFalseDeadlockPre.isFalse() << "\n";
                    BF testForTrueDeadlockPost = ( (remainingTransitions & variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    BF testForFalseDeadlockPost = ( (remainingTransitions & !variables[varIdxDeadlockPost[j]]).ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]) );
                    // std::cerr << "   iteration: " << iter << "  testIfChangingPost: " << !testForTrueDeadlockPost.isFalse() << !testForFalseDeadlockPost.isFalse() << "\n";

                    // testIfChanging |= ( !testForTrueDeadlockPre.isFalse() & testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() ); // | ( testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse() );
                    bool testIfChangingTmp = testForTrueDeadlockPre.isFalse() & !testForFalseDeadlockPre.isFalse() & !testForTrueDeadlockPost.isFalse() & testForFalseDeadlockPost.isFalse();

                    if (testIfChangingTmp){
                        int number = deadlockVariableVector[j];
                        // Loop over all robots involved in this deadlock sensor proposition to single out the 'weakest' restrictions to the env - i.e. prevent all exits from becoming blocked
                        while (number) {
                            std::stringstream robotID;
                            robotID << "m_rob" << number%10 << "_deadlock";
                            number /= 10;
                            for (unsigned int j1=0;j1<variableNames.size();j1++) {
                                if ( variableNames[j1].compare(0,robotID.str().size(),robotID.str()) == 0 ) {
                                    BF testForTrueMemProp = ( (remainingTransitions & variables[j1]).ExistAbstractSingleVar(variables[j1]) );
                                    BF testForFalseMemProp = ( (remainingTransitions & !variables[j1]).ExistAbstractSingleVar(variables[j1]) );
                                    // std::cerr << "    memprop " << variableNames[j1] << " " << bool( !testForTrueMemProp.isFalse() & testForFalseMemProp.isFalse() ) << "\n";
                                    // If any of the memory propositions are already set, then save the cut and break the loop.
                                    // NB: this is temporary and assumes that all regions have exactly two faces.
                                    if ( !testForTrueMemProp.isFalse() & testForFalseMemProp.isFalse() ) {
                                        std::cerr << "    memprop " << variableNames[j1] << "\n";
                                        std::cerr << "    cut found for: " << variableNames[varIdxDeadlockPre[j]] << "\n";
                                        testIfChanging.push_back(testIfChangingTmp);
                                        idxDeadlockRisingEdge.push_back(j);
                                        break;
                                    }
                                }
                            }
                        }

                        if (testIfChanging.size() == 0) {
                            std::cerr << " **** failed to find any weak conditions.\n";
                            testIfChangingStrongRestriction.clear();
                            testIfChangingStrongRestriction.push_back(testIfChangingTmp);
                            idxDeadlockRisingEdgeStrongRestriction.clear();
                            idxDeadlockRisingEdgeStrongRestriction.push_back(j);
                        }
                    }
                }

                // If no weak conditions can be found in this counterstrategy, apply a stronger condition to the env instead.
                // candidateCutConditionsArrayStrongRestriction.push_back(transitionsAsImplication);
                // candidateCutConditionsArrayStrongRestrictionVisualOnly.push_back(transitionsWithoutDeadlock & postDeadlockCut);

                // Save the entire set of cuts if weak conditions found; otherwise store exactly one cut (as another variable) as a strengthened restriction for this counterstrategy.
                // std::cout << " testIfChanging: " << testIfChanging.size() << "\n";
                // std::cout << " testIfChangingStrongRestriction: " << testIfChangingStrongRestriction.size() << "\n";
                if (testIfChanging.size() > 0 || testIfChangingStrongRestriction.size() > 0 ) {
                    BF transitionsWithoutDeadlock = remainingTransitions;
                    BF postDeadlockCut = mgr.constantFalse();

                    if (testIfChangingStrongRestriction.size() > 0) {
                        idxDeadlockRisingEdge = idxDeadlockRisingEdgeStrongRestriction;
                    }
                    for (unsigned int j=0;j<varIdxDeadlockPost.size();j++) {
                        // std::cerr << "    testing variable: " << varIdxDeadlockPost[j] << variableNames[varIdxDeadlockPost[j]] << "\n";
                        bool isRisingEdge = false;
                        for (unsigned int jv=0;jv<idxDeadlockRisingEdge.size();jv++) {
                            if (idxDeadlockRisingEdge[jv] == j) {
                                isRisingEdge = true;
                                postDeadlockCut |= variables[varIdxDeadlockPost[j]];  //we're at a rising edge, so this variable is always true
                            }
                        }
                        // BF_newDumpDot(*this,postDeadlockCut,"PreInput PreOutput PostInput PostOutput","/tmp/postDeadlockCut.dot");
                        if (!isRisingEdge) {
                            // std::cerr << "    abstracting out variable: " << variableNames[varIdxDeadlockPost[j]] << "\n";
                            transitionsWithoutDeadlock = transitionsWithoutDeadlock.ExistAbstractSingleVar(variables[varIdxDeadlockPost[j]]);
                        }
                    }

                    for (unsigned int j=0;j<varIdxDeadlockPre.size();j++) {
                        // std::cerr << "    testing variable: " << varIdxDeadlockPost[j] << variableNames[varIdxDeadlockPre[j]] << "\n";
                        bool isRisingEdge = false;
                        for (unsigned int jv=0;jv<idxDeadlockRisingEdge.size();jv++) {
                            if (idxDeadlockRisingEdge[jv] == j) {
                                isRisingEdge = true;
                            }
                        }
                        if (!isRisingEdge) {
                            // std::cerr << "    abstracting out variable: " << variableNames[varIdxDeadlockPre[j]] << "\n";
                            transitionsWithoutDeadlock = transitionsWithoutDeadlock.ExistAbstractSingleVar(variables[varIdxDeadlockPre[j]]);
                        }
                    }
                    // for (unsigned int j=0;j<testIfChanging.size();j++) {
                    //     transitionsWithoutDeadlock &= deadlockVarsChanging[j];
                    // }

                    std::cerr << "   iteration: " << iter << " to be cut.\n";
                    numFound++;

                    BF_newDumpDot(*this,!postDeadlockCut.ExistAbstract(varCubePre),"PreInput PreOutput PostInput PostOutput","/tmp/postDeadlockCut.dot");
                    BF transitionsAsImplication = (transitionsWithoutDeadlock).Implies(!postDeadlockCut);
                    // BF transitionsAsImplication = (transitionsWithoutDeadlock.ExistAbstract(varCubePost)).Implies(transitionsWithoutDeadlock.ExistAbstract(varCubePostOutput).ExistAbstract(varCubePre) & !postDeadlockCut);
                    BF_newDumpDot(*this,transitionsWithoutDeadlock & postDeadlockCut,"PreInput PreOutput PostInput PostOutput","/tmp/livenessCutsSingleVisual.dot");
                    BF_newDumpDot(*this,transitionsAsImplication,"PreInput PreOutput PostInput PostOutput","/tmp/livenessCuts.dot");
                    // std::stringstream fname;
                    // fname << "/tmp/livenessCuts" << iter << ".dot";
                    // BF_newDumpDot(*this,transitionsAsImplication,"PreInput PreOutput PostInput PostOutput",fname.str());

                    if (testIfChanging.size() > 0) {
                        candidateCutConditionsArray.push_back(transitionsAsImplication);
                        candidateCutConditionsArrayVisualOnly.push_back(transitionsWithoutDeadlock & postDeadlockCut);
                    } else {
                        candidateCutConditionsArrayStrongRestriction.clear();
                        candidateCutConditionsArrayStrongRestrictionVisualOnly.clear();
                        candidateCutConditionsArrayStrongRestriction.push_back(transitionsAsImplication);
                        candidateCutConditionsArrayStrongRestrictionVisualOnly.push_back(transitionsWithoutDeadlock & postDeadlockCut);
                    }
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

                    if (saveCounterstrategy) {
                        // Print
                        if (first) {
                            first = false;
                        } else {
                            outputStream << ", ";
                        }
                        outputStream << tn;
                    }

                }
            }

            if (saveCounterstrategy) {outputStream << "\n";}
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

      void addDeadlocked(BF targetPositionCandidateSet, std::pair<size_t, std::pair<unsigned int, unsigned int> > current, std::vector<BF> &bfsUsedInTheLookupTable, std::map<std::pair<size_t, std::pair<unsigned int, unsigned int> >, unsigned int > &lookupTableForPastStates, std::ostream &outputStream, BF &deadlockCut) {

        BF newCombination = determinize(targetPositionCandidateSet, postVars) ;

        newCombination  = (newCombination.ExistAbstract(varCubePostOutput).ExistAbstract(varCubePre)).SwapVariables(varVectorPre,varVectorPost);

        unsigned int stateNum = lookupTableForPastStates[current];
        BF currentPossibilities = bfsUsedInTheLookupTable[stateNum];

        //cut to exclude current transition from counterstrategy
        deadlockCut &= currentPossibilities.Implies(!newCombination.SwapVariables(varVectorPost,varVectorPre));
        // deadlockCut &= (currentPossibilities.ExistAbstract(varCubePost)).Implies(!newCombination.SwapVariables(varVectorPre,varVectorPost).ExistAbstract(varCubePre).ExistAbstract(varCubePostOutput));

        if (saveCounterstrategy) {
            std::pair<size_t, std::pair<unsigned int, unsigned int> > target = std::pair<size_t, std::pair<unsigned int, unsigned int> >(newCombination.getHashCode(),std::pair<unsigned int, unsigned int>(current.second.first, current.second.second));
            unsigned int tn;

            if (lookupTableForPastStates.count(target)==0) {
                tn = lookupTableForPastStates[target] = bfsUsedInTheLookupTable.size();
                bfsUsedInTheLookupTable.push_back(newCombination);
                outputStream << tn << "\n";

                //Note that since we are printing here, we usually end up with the states being printed out of order.
                //TOTO: print in order
                outputStream << "State " << tn << " with rank (" << current.second.first << "," << current.second.second << ") -> <";
                bool first = true;
                for (unsigned int i=0;i<variables.size();i++) {
                    if (doesVariableInheritType(i,PreInput)) {
                        if (first) {
                            first = false;
                        } else {
                            outputStream << ", ";
                        }
                        outputStream << variableNames[i] << ":";
                        outputStream << (((newCombination & variables[i]).isFalse())?"0":"1");
                    }
                }
                outputStream << ">\n\tWith no successors.";

            } else {
                tn = lookupTableForPastStates[target];
                outputStream << tn;
            }
        }
    }
}

#endif // FINDREVISIONS_H
