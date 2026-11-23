module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOp
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

@[expose] public section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.isCompl_orth_of_definite {E : Type} [Field E] [NumberField E] [StarRing E]
    (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V)
    (hpos : ∀ x ∈ orth S U, x ≠ 0 → 0 < Algebra.trace ℚ E (S.hT x x)) :
    IsCompl U (orth S U) := by
  have hmem : ∀ v, v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
    intro v
    simp [orth, Submodule.mem_iInf, LinearMap.mem_ker]
  have hdis : U ⊓ orth S U = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases hx with ⟨hxU, hxO⟩
    by_contra hne
    have h0 : S.hT x x = 0 := (hmem x).1 hxO x hxU
    have := hpos x hxO hne
    rw [h0, map_zero] at this
    exact lt_irrefl _ this
  let b := Module.finBasis E U
  let φ : S.V →ₗ[E] (Fin (Module.finrank E U) → E) := LinearMap.pi fun i => S.hT (b i : S.V)
  have hker : LinearMap.ker φ ≤ orth S U := by
    intro y hy
    rw [LinearMap.mem_ker] at hy
    rw [hmem]
    intro x hx
    have hy' : ∀ i, S.hT (b i : S.V) y = 0 := fun i => congrFun hy i
    have hx' : (⟨x, hx⟩ : U) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
    have hxs : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : S.V) := by
      have := congrArg (Subtype.val) hx'
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this

    rw [hxs, map_sum]
    simp [LinearMap.sum_apply, hy']
  have hrk : Module.finrank E S.V ≤ Module.finrank E U + Module.finrank E (orth S U) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    have h2 : Module.finrank E (LinearMap.range φ) ≤ Module.finrank E U := by
      have := Submodule.finrank_le (LinearMap.range φ)
      simpa using this
    have h3 := Submodule.finrank_mono hker
    omega
  have hcod : U ⊔ orth S U = ⊤ := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U (orth S U)
    rw [hdis, finrank_bot] at h
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_le (U ⊔ orth S U)
    omega
  exact ⟨disjoint_iff.2 hdis, codisjoint_iff.2 hcod⟩
