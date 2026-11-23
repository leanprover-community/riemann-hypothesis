module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMonStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupLocalKummerNormsNeTopStatement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
