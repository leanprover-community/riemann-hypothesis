module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.Published GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a), Paired π π' conjOp → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π'.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  first | exact @GlobalTheory.CapPair.infChar_conj_of_paired
