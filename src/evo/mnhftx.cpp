// Copyright (c) 2017-2021 The Dash Core developers
// Distributed under the MIT software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include <evo/mnhftx.h>
#include <llmq/commitment.h>
#include <llmq/signing.h>
#include <evo/specialtx.h>
#include <consensus/validation.h>

#include <chain.h>
#include <chainparams.h>
#include <logging.h>
#include <validation.h>

extern const std::string CBLSIG_REQUESTID_PREFIX = "clsig";

bool MNHFTx::Verify(const CBlockIndex* pQuorumIndex) const
{
    if (nVersion == 0 || nVersion > CURRENT_VERSION) {
        return false;
    }

    Consensus::LLMQType llmqType = Params().GetConsensus().llmqTypeMnhf;
    int signOffset{llmq::GetLLMQParams(llmqType).dkgInterval};

    const uint256 requestId = ::SerializeHash(std::make_pair(CBLSIG_REQUESTID_PREFIX, pQuorumIndex->nHeight));
    if(llmq::quorumSigningManager->VerifyRecoveredSig(llmqType, pQuorumIndex->nHeight, requestId, pQuorumIndex->GetBlockHash(), sig, 0) ||
            llmq::quorumSigningManager->VerifyRecoveredSig(llmqType, pQuorumIndex->nHeight, requestId, pQuorumIndex->GetBlockHash(), sig, signOffset)) {
        if (!sig.IsValid()) {
           return false;
        }
    }

    return true;
}

bool CheckMNHFTx(const CTransaction& tx, const CBlockIndex* pindexPrev, CValidationState& state) EXCLUSIVE_LOCKS_REQUIRED(cs_main)
{
    MNHFTxPayload mnhfTx;
    if (!GetTxPayload(tx, mnhfTx)) {
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-payload");
    }

    if (mnhfTx.nVersion == 0 || mnhfTx.nVersion > MNHFTxPayload::CURRENT_VERSION) {
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-version");
    }

    const CBlockIndex* pindexQuorum = LookupBlockIndex(mnhfTx.signal.quorumHash);
    if (!pindexQuorum) {
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-quorum-hash");
    }
    
    if (pindexQuorum != pindexPrev->GetAncestor(pindexQuorum->nHeight)) {
        // not part of active chain
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-quorum-hash");
    }

    if (!Params().GetConsensus().llmqs.count(Params().GetConsensus().llmqTypeMnhf)) {
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-type");
    }

    if (!mnhfTx.signal.Verify(pindexQuorum)) {
        return state.DoS(100, false, REJECT_INVALID, "bad-mnhf-invalid");
    }

    return true;
}

std::string MNHFTx::ToString() const
{
    return strprintf("MNHFTx(nVersion=%d, quorumHash=%s, sig=%s)",
        nVersion, quorumHash.ToString(), sig.ToString());
}
