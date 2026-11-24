module

public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
import Formalism.LocalToGlobal.ProjectiveLattices.JFDFree
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Localization.Finiteness
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.SelfDualIsom

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {M₁ M₂ V : Type}
    [AddCommGroup M₁] [Module (𝓞 E) M₁] [Module.Finite (𝓞 E) M₁]
    [AddCommGroup M₂] [Module (𝓞 E) M₂] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] (φ₁ : M₁ →ₗ[𝓞 E] V) (φ₂ : M₂ →ₗ[𝓞 E] V)
    (hspan : Submodule.span E (Set.range φ₂) = ⊤) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, (N : 𝓞 E) • φ₁ x ∈ LinearMap.range φ₂ := by
  classical
  have h1 : ∀ v : V, ∃ n : ℕ, 0 < n ∧ (n : 𝓞 E) • v ∈ LinearMap.range φ₂ := by
    intro v
    have hv : v ∈ Submodule.span E (Set.range φ₂) := by rw [hspan]; trivial
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E _ v hv
    rw [← LinearMap.coe_range, Submodule.span_eq] at ht
    have ht0 : (t : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero t.2
    have hm := Ideal.absNorm_mem (Ideal.span {(t : 𝓞 E)})
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hm
    refine ⟨Ideal.absNorm (Ideal.span {(t : 𝓞 E)}), Nat.pos_of_ne_zero ?_, ?_⟩
    · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
      exact ht0
    · rw [← hc, mul_smul]
      exact Submodule.smul_mem _ _ ht
  choose n hn hmem using h1
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M₁)
  refine ⟨∏ x ∈ s, n (φ₁ x), Finset.prod_pos fun x _ => hn _, fun x => ?_⟩
  have hx : x ∈ Submodule.span (𝓞 E) (s : Set M₁) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ₁ x)) (Finset.mem_coe.1 hy)
    rw [hk, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ (hmem _)
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul, smul_comm]; exact Submodule.smul_mem _ _ ha

end GlobalTheory.SelfDualIsom
