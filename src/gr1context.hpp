//=====================================================================
// General data structures for GR(1) synthesis
//=====================================================================
#ifndef __GR1CONTEXT_HPP__
#define __GR1CONTEXT_HPP__

#include "BF.h"
#include <set>
#include <vector>
#include "bddDump.h"

typedef enum { PreInput, PreOutput, PostInput,PostOutput } VariableType;

/**
 * @brief Container class for all GR(1) synthesis related activities
 *        Modifications of the GR(1) synthesis algorithm
 *        (or strategy extraction) should derive from this class, as it
 *        provides input parsing and BF/BDD book-keeping.
 */
class GR1Context : public VariableInfoContainer {
protected:

    //@{
    /** @name BF-related stuff that is computed in the constructor, i.e., with loading the input specification
     */
    BFManager mgr;
    std::vector<BF> variables;
    std::vector<std::string> variableNames;
    std::vector<VariableType> variableTypes;
    std::vector<BF> livenessAssumptions;
    std::vector<BF> livenessGuarantees;
    BF initEnv;
    BF initSys;
    BF safetyEnv;
    BF safetySys;
    BFVarVector varVectorPre;
    BFVarVector varVectorPost;
    BFVarCube varCubePostInput;
    BFVarCube varCubePostOutput;
    BFVarCube varCubePreInput;
    BFVarCube varCubePreOutput;
    BFVarCube varCubePre;
    std::vector<BF> preVars;
    std::vector<BF> postVars;
    //@}

    //@{
    /** @name Information that is computed during realizability checking
     *  The following variables are set by the realizability checking part. The first one
     *  contains information to be used during strategy extraction - it prodives a sequence
     *  of BFs/BDDs that represent transitions in the game that shall be preferred over those
     *  that come later in the vector. The 'uint' data type in the vector represents the goal
     *  that a BF refers to. The winningPositions BF represents which positions are winning for the system player.
     */
    std::vector<std::pair<uint,BF> > strategyDumpingData;
    BF winningPositions;
    //@}

private:
    // The following variables is only used during parsing the input instance.
    // It allows us to get better error messages for parsing.
    uint lineNumberCurrentlyRead;

    // Internal functions - these are used during parsing an input instance
    BF parseBooleanFormulaRecurse(std::istringstream &is,std::set<VariableType> &allowedTypes);
    BF parseBooleanFormula(std::string currentLine,std::set<VariableType> &allowedTypes);

public:
    GR1Context(const char *inFilename);
    virtual ~GR1Context() {}
    virtual bool checkRealizability();
    virtual void computeAndPrintExplicitStateStrategy();

    // ===========================================================
    // The following functions are inherited from the VariableInfo
    // container. They allow us to the the BF_dumpDot function
    // for debugging new variants of the synthesis algorithm
    // ===========================================================
    void getVariableTypes(std::vector<std::string> &types) const {
        types.push_back("PreInput");
        types.push_back("PreOutput");
        types.push_back("PostInput");
        types.push_back("PostOutput");
    }

    void getVariableNumbersOfType(std::string typeString, std::vector<uint> &nums) const {
        VariableType type;
        if (typeString=="PreInput") type = PreInput;
        else if (typeString=="PreOutput") type = PreOutput;
        else if (typeString=="PostInput") type = PostInput;
        else if (typeString=="PostOutput") type = PostOutput;
        else throw "Cannot detect variable type for BDD dumping";
        for (uint i=0;i<variables.size();i++) {
            if (variableTypes[i] == type) nums.push_back(i);
        }
    }

    virtual BF getVariableBF(uint number) const {
        return variables[number];
    }

    virtual std::string getVariableName(uint number) const {
        return variableNames[number];
    }
};


/**
 * @brief Helper class for easier BF-based fixed point computation
 */
class BFFixedPoint {
private:
    BF currentValue;
    bool reachedFixedPoint;
public:
    BFFixedPoint(BF init) : currentValue(init), reachedFixedPoint(false) {}
    void update(BF newOne) {
        if (currentValue == newOne) {
            reachedFixedPoint = true;
        } else {
            currentValue = newOne;
        }
    }
    bool isFixedPointReached() const { return reachedFixedPoint; }
    BF getValue() { return currentValue; }
};


#endif
