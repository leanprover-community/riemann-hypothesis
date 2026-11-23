module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BCT ValuativeRel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ModCompactParab

theorem deltaHalf_leviProj_eq_one_of_isCompact :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b n : ℕ)
      (e : Fin a ⊕ Fin b ≃ Fin n) (K : Subgroup (GL (Fin n) k)), IsCompact (K : Set (GL (Fin n) k)) →
      ∀ p : parab k (two e), (p : GL (Fin n) k) ∈ K →
        deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) = 1 := by
  intro k _ _ _ _ a b n e K hK p hp
  let χ : parab k (two e) →* ℂˣ := (deltaHalf k (Two (Fin a) (Fin b))).comp (leviProj k (two e))
  have hχ : Continuous (leviProj k (two e)) := GlobalTheory.ParabLevel.continuous_leviProj (R := k) (two e)
  have hemb : Topology.IsClosedEmbedding (Subtype.val : parab k (two e) → GL (Fin n) k) :=
    (GlobalTheory.ParabLevel.isClosed_parab_two (R := k) e).isClosedEmbedding_subtypeVal
  let H : Subgroup (parab k (two e)) := K.subgroupOf (parab k (two e))
  have hH : IsCompact (H : Set (parab k (two e))) := hemb.isCompact_preimage hK
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hH
  have hopen : IsOpen ((χ.ker.subgroupOf H : Subgroup H) : Set H) :=
    (isSmoothChar_deltaHalf k (m := Two (Fin a) (Fin b))).preimage (hχ.comp continuous_subtype_val)
  haveI : Finite (H ⧸ χ.ker.subgroupOf H) := Subgroup.quotient_finite_of_isOpen _ hopen
  have hidx : (χ.ker.subgroupOf H).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  obtain ⟨m, hm, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx (⟨p, hp⟩ : H)
  have hpow : deltaHalf k (Two (Fin a) (Fin b)) (leviProj k (two e) p) ^ m = 1 := by
    have h := Subgroup.mem_subgroupOf.1 hmem
    simpa [χ, MonoidHom.mem_ker, map_pow] using h
  have hreal : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) ^ m = 1 := by
    have h := congrArg (fun u : ℂˣ => (u : ℂ)) hpow
    simp only [Units.val_pow_eq_pow_val, val_deltaHalf, Units.val_one] at h
    exact_mod_cast h
  have hone : (√(modulus k (Two (Fin a) (Fin b)) (leviProj k (two e) p)) : ℝ) = 1 :=
    (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) hm.ne').1 hreal
  ext
  rw [val_deltaHalf, hone]
  simp

end GlobalTheory.CompanionTheory.ModCompactParab
