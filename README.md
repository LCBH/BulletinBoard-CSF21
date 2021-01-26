This repository includes the companion technical report and the TLA+ proofs for the paper "Fixing the Achilles Heel of E-Voting: The Bulletin Board" published at IEEE Computer Security Foundations 2021. 

# Companion technical report
The extended version of the paper can be found as an [IACR preprint](https://eprint.iacr.org/2020/109).

# TLA+ Proofs
We define a decentralized bulletin board (BB) for e-voting protocols
that minimize the trust assumptions (in terms of the number of peers
that need to be trusted) while providing the requirements we have
identified for a BB, that is final-agreement (FA). For all
specifications, we assume a set of all possible BB contents (W)
equipped with an extension relation (extends/extendsB) that expresses
when a BB content extends another BB content. W and extends can
typically be instantiated by 'W = SUBSET Items' (where Items is the
set of all items that can be in a BB content) and 'Extends =
\subseteq'.

## Abstractions
FA only imposes restrictions on B(s.fc), B(s.nfc), that is:
  \/ B(s.fc) = {}
  \/ \exists B_f, B(s.fc) = {B_f} /\ B(s.nfc) \extendseq B(s.fc).
Therefore, we shall only store in dedicated state variables the BB
contents B that are read through:
  (i)  Read-nonFinal and that are normally added to a processed check
       (C,x,a,B) in s.nfc and
  (ii) Read-Final and that are normally added to a processed check
       (C,x,a,B) in s.fc.
The former BB contents are added to the state variable c and the
latter are added to f.  Formally, one has that c = B(s.nfc) and
f=G(s.fc).

## Specifications
The specification of our protocol and FA and the proof that the former
meets the latter are included in the file `BB_FA.tla`.

A PDF automatically generated from the specification in plaintext can
be found in `BB_FA.pdf`.

# Reproduction
## Installing TLA+ and documentation
See
 - http://lamport.azurewebsites.net/tla/tla.html for the toolbox (IDE)
   and
 - http://tla.msr-inria.inria.fr/tlaps/content/Home.html for TLAPS
   (proof theorem assistant embedded in TLA+).

## Recheck the proofs
Open the file `BB_FA.tla` with TLA+ and use the shortcut Ctrl-G Ctrl-G
to run TLAPS on all the lemma, property, and theorem statements. The
proof verification takes ca. 1 minute in total.
