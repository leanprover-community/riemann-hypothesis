module

public import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add (f := _)]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add (f := _)]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

end Examples

end GlobalTheory.UPel.Sm.Model
