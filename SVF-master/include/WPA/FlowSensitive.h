//===- FlowSensitive.h -- Flow-sensitive pointer analysis---------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

/*
 * FlowSensitiveAnalysis.h
 *
 *  Created on: Oct 28, 2013
 *      Author: Yulei Sui
 */

#ifndef FLOWSENSITIVEANALYSIS_H_
#define FLOWSENSITIVEANALYSIS_H_

#include "MSSA/SVFGOPT.h"
#include "MSSA/SVFGBuilder.h"
#include "WPA/WPAFSSolver.h"
class AndersenWaveDiff;

/*!
 * Flow sensitive whole program pointer analysis
 */
typedef WPAFSSolver<SVFG*> WPASVFGFSSolver;
class FlowSensitive : public WPASVFGFSSolver, public BVDataPTAImpl {
    friend class FlowSensitiveStat;
private:
    typedef SVFG::SVFGEdgeSetTy SVFGEdgeSetTy;

public:
    typedef BVDataPTAImpl::IncDFPTDataTy::DFPtsMap DFInOutMap;
    typedef BVDataPTAImpl::IncDFPTDataTy::PtsMap PtsMap;

    /// Constructor
    FlowSensitive(PTATY type = FSSPARSE_WPA) : WPASVFGFSSolver(), BVDataPTAImpl(type)
    {
        svfg = NULL;
        solveTime = sccTime = processTime = propagationTime = updateTime = 0;
        addrTime = copyGepTime = loadTime = storeTime = 0;
        updateCallGraphTime = directPropaTime = indirectPropaTime = 0;
        numOfProcessedAddr = numOfProcessedCopy = numOfProcessedGep = 0;
        numOfProcessedLoad = numOfProcessedStore = 0;
        numOfProcessedPhi = numOfProcessedActualParam = numOfProcessedFormalRet = 0;
        numOfProcessedMSSANode = 0;
        maxSCCSize = numOfSCC = numOfNodesInSCC = 0;
    }

    /// Destructor
    virtual ~FlowSensitive() {
        if (svfg != NULL)
            delete svfg;
        svfg = NULL;
    }

    /// Create signle instance of flow-sensitive pointer analysis
    static FlowSensitive* createFSWPA(llvm::Module& module) {
        if (fspta == NULL) {
            fspta = new FlowSensitive();
            fspta->analyze(module);
        }
        return fspta;
    }

    /// Release flow-sensitive pointer analysis
    static void releaseFSWPA() {
        if (fspta)
            delete fspta;
        fspta = NULL;
    }

    /// We start from here
    virtual bool runOnModule(llvm::Module& module) {
        /// start analysis
        analyze(module);
        return false;
    }

    /// Flow sensitive analysis
    virtual void analyze(llvm::Module& module);

    /// Initialize analysis
    virtual void initialize(llvm::Module& module);

    /// Finalize analysis
    virtual void finalize();

    /// Get PTA name
    virtual const std::string PTAName() const {
        return "FlowSensitive";
    }

    /// Methods for support type inquiry through isa, cast, and dyn_cast
    //@{
    static inline bool classof(const FlowSensitive *) {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta) {
        return pta->getAnalysisTy() == FSSPARSE_WPA;
    }
    //@}

    /// Return SVFG
    inline SVFG* getSVFG() const {
        return svfg;
    }

protected:
    /// SCC detection
    virtual NodeStack& SCCDetect();

    /// Propagation
    //@{
    /// Propagate points-to information from an edge's src node to its dst node.
    virtual bool propFromSrcToDst(SVFGEdge* edge);
    /// Propagate points-to information along a DIRECT SVFG edge.
    virtual bool propAlongDirectEdge(const DirectSVFGEdge* edge);
    /// Propagate points-to information along an INDIRECT SVFG edge.
    virtual bool propAlongIndirectEdge(const IndirectSVFGEdge* edge);
    /// Propagate points-to information of a certain variable from src to dst.
    virtual bool propVarPtsFromSrcToDst(NodeID var, const SVFGNode* src, const SVFGNode* dst);
    /// Propagate points-to information from an actual-param to a formal-param.
    /// Not necessary if SVFGOPT is used instead of original SVFG.
    virtual bool propagateFromAPToFP(const ActualParmSVFGNode* ap, const SVFGNode* dst);
    /// Propagate points-to information from a formal-ret to an actual-ret.
    /// Not necessary if SVFGOPT is used instead of original SVFG.
    virtual bool propagateFromFRToAR(const FormalRetSVFGNode* fr, const SVFGNode* dst);
    /// Handle weak updates
    virtual bool weakUpdateOutFromIn(const SVFGNode* node) {
        return getDFPTDataTy()->updateAllDFOutFromIn(node->getId(),0,false);
    }
    /// Handle strong updates
    virtual bool strongUpdateOutFromIn(const SVFGNode* node, NodeID singleton) {
        return getDFPTDataTy()->updateAllDFOutFromIn(node->getId(),singleton,true);
    }
    //@}

    /// Propagation between newly connected SVFG nodes during updateCallGraph.
    /// Can only be used during updateCallGraph.
    //@{
    bool propVarPtsAfterCGUpdated(NodeID var, const SVFGNode* src, const SVFGNode* dst);

    inline bool propDFOutToIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) {
        return getDFPTDataTy()->updateAllDFInFromOut(srcStmt->getId(), srcVar, dstStmt->getId(),dstVar);
    }
    inline bool propDFInToIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) {
        return getDFPTDataTy()->updateAllDFInFromIn(srcStmt->getId(), srcVar, dstStmt->getId(),dstVar);
    }
    //@}

    /// Update data-flow points-to data
    //@{
    inline bool updateOutFromIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) {
        return getDFPTDataTy()->updateDFOutFromIn(srcStmt->getId(),srcVar, dstStmt->getId(),dstVar);
    }
    inline bool updateInFromIn(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) {
        return getDFPTDataTy()->updateDFInFromIn(srcStmt->getId(),srcVar, dstStmt->getId(),dstVar);
    }
    inline bool updateInFromOut(const SVFGNode* srcStmt, NodeID srcVar, const SVFGNode* dstStmt, NodeID dstVar) {
        return getDFPTDataTy()->updateDFInFromOut(srcStmt->getId(),srcVar, dstStmt->getId(),dstVar);
    }

    inline bool unionPtsFromIn(const SVFGNode* stmt, NodeID srcVar, NodeID dstVar) {
        return getDFPTDataTy()->updateTLVPts(stmt->getId(),srcVar,dstVar);
    }
    inline bool unionPtsFromTop(const SVFGNode* stmt, NodeID srcVar, NodeID dstVar) {
        return getDFPTDataTy()->updateATVPts(srcVar,stmt->getId(),dstVar);
    }

    inline void clearAllDFOutVarFlag(const SVFGNode* stmt) {
        getDFPTDataTy()->clearAllDFOutUpdatedVar(stmt->getId());
    }
    //@}

    /// Handle various constraints
    //@{
    virtual void processNode(NodeID nodeId);
    bool processSVFGNode(SVFGNode* node);
    bool processAddr(const AddrSVFGNode* addr);
    bool processCopy(const CopySVFGNode* copy);
    bool processPhi(const PHISVFGNode* phi);
    bool processGep(const GepSVFGNode* edge);
    bool processLoad(const LoadSVFGNode* load);
    bool processStore(const StoreSVFGNode* store);
    //@}

    /// Update call graph
    //@{
    /// Update call graph.
    bool updateCallGraph(const CallSiteToFunPtrMap& callsites);
    /// Connect nodes in SVFG.
    void connectCallerAndCallee(const CallEdgeMap& newEdges, SVFGEdgeSetTy& edges);
    /// Update nodes connected during updating call graph.
    virtual void updateConnectedNodes(const SVFGEdgeSetTy& edges);
    //@}

    /// Return TRUE if this is a strong update STORE statement.
    bool isStrongUpdate(const SVFGNode* node, NodeID& singleton);

    SVFG* svfg;
private:
    ///Get points-to set for a node from data flow IN/OUT set at a statement.
    //@{
    inline const PointsTo& getDFInPtsSet(const SVFGNode* stmt, const NodeID node) {
        return getDFPTDataTy()->getDFInPtsSet(stmt->getId(),node);
    }
    inline const PointsTo& getDFOutPtsSet(const SVFGNode* stmt, const NodeID node) {
        return getDFPTDataTy()->getDFOutPtsSet(stmt->getId(),node);
    }
    //@}

    ///Get IN/OUT data flow map;
    //@{
    inline const DFInOutMap& getDFInputMap() const {
        return getDFPTDataTy()->getDFIn();
    }
    inline const DFInOutMap& getDFOutputMap() const {
        return getDFPTDataTy()->getDFOut();
    }
    //@}

    static FlowSensitive* fspta;
    SVFGBuilder memSSA;

    /// Statistics.
    //@{
    Size_t numOfProcessedAddr;	/// Number of processed Addr node
    Size_t numOfProcessedCopy;	/// Number of processed Copy node
    Size_t numOfProcessedGep;	/// Number of processed Gep node
    Size_t numOfProcessedPhi;	/// Number of processed Phi node
    Size_t numOfProcessedLoad;	/// Number of processed Load node
    Size_t numOfProcessedStore;	/// Number of processed Store node
    Size_t numOfProcessedActualParam;	/// Number of processed actual param node
    Size_t numOfProcessedFormalRet;	/// Number of processed formal ret node
    Size_t numOfProcessedMSSANode;	/// Number of processed mssa node

    Size_t maxSCCSize;
    Size_t numOfSCC;
    Size_t numOfNodesInSCC;

    double solveTime;	///< time of solve.
    double sccTime;	///< time of SCC detection.
    double processTime;	///< time of processNode.
    double propagationTime;	///< time of points-to propagation.
    double directPropaTime;	///< time of points-to propagation of address-taken objects
    double indirectPropaTime; ///< time of points-to propagation of top-level pointers
    double updateTime;	///< time of strong/weak updates.
    double addrTime;	///< time of handling address edges
    double copyGepTime;	///< time of handling copy and gep edges
    double loadTime;	///< time of load edges
    double storeTime;	///< time of store edges
    double updateCallGraphTime; ///< time of updating call graph

    NodeBS svfgHasSU;
    //@}

};

#endif /* FLOWSENSITIVEANALYSIS_H_ */