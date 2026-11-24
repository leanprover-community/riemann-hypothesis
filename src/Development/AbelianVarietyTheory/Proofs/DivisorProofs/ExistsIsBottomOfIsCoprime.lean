module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CondEIsCoprimeHalfDifferent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBetaInvHeckeU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberReferenceTupleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairSmallMemberReferenceTupleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUAlphaH
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeUNuInv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.SqNum

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}

theorem exists_isBottom_of_isCoprime (hL : L.Is μ₀) (G : GridData L sc)
    (hm : IsCoprime (condE G.pl) D.host.𝔟) (hm' : IsCoprime (D.host.conj • condE G.pl) D.host.𝔟) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' := by
  obtain ⟨δ, hδ⟩ := GlobalTheory.NormSum.exists_crv_top D
  obtain ⟨t0, ht⟩ := (GlobalTheory.TwoTorsionPt.exists_point D ⊤ δ hδ).1
  refine ⟨δ, t0, fun i j => ?_⟩
  obtain ⟨χν, hν, hw⟩ := GlobalTheory.BottomNu.exists_heckeU_nu_inv hL G i j
  obtain ⟨χβ, hβ⟩ := exists_betaInv_heckeU hL G i j
  obtain ⟨χα, hα⟩ := exists_heckeU_alphaH hL G i j
  obtain ⟨P, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.exists_bottomPair_bigMember_reference_tuple hL G hm hδ ht i j χβ hβ χν hν hw
  obtain ⟨P', h1', h2', h3', h4', h5'⟩ := GlobalTheory.T.exists_bottomPair_smallMember_reference_tuple hL G hm' hδ ht i j χα hα χν hν hw
  exact ⟨P, P', ⟨⟨h1, h1', h2, h2'.trans h2.symm⟩, h3, h3', h4, h4', ⟨h5, h5'⟩⟩⟩

theorem exists_isBottom (hL : L.Is μ₀) (G : GridData L sc) (hq : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) :
    ∃ δ t0 : ℂ, ∀ i j : Fin D.R.m, ∃ P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 (levQ G.pl),
      IsBottom G μ₀ i j (condE G.pl) P P' :=
  exists_isBottom_of_isCoprime hL G (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).1
    (GlobalTheory.FunObj.StdDatum.HalfDiff.condE_isCoprime_halfDifferent G.pl hq).2

end GlobalTheory.FunObj.SqNum
