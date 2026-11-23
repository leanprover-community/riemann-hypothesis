module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.SpanXLeKerAevalZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem cup_per_sum_const {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc)
    (β : Λ → Λ → Hol F.V)
    (h : (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
    (hℓ : ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) =
      (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) :
    ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg) := by
  simp only [Charts.perCl, GlobalTheory.CatCoh.cup_mk] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, GlobalTheory.CatCoh.H2.mk_eq_mk] at h
  obtain ⟨f, hf⟩ := h
  refine ⟨f + c, fun T T' T'' φ ψ ↦ ?_⟩
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hf T) T') T'') φ) ψ
  have e2 := hℓ T T' T'' φ ψ
  rw [map_add (f := _), Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, Pi.add_apply, e]
  rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Submodule.coe_sum]
  simp only [Finset.sum_apply, GlobalTheory.CatCoh.cupZ_apply, Charts.perZ, Charts.mp_Oc] at e2 ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e2, map_sub, map_sum]
  simp only [AlgHom.commutes, map_mul]
  ring

end GlobalTheory.AnPer
