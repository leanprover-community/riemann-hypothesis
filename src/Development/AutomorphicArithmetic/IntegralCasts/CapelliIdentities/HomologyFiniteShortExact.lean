module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Category.Grp.IsFinite
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.RingTheory.Noetherian.Basic

@[expose] public section

open CategoryTheory

namespace UpperTheory

universe v u w

private lemma finite_middle {R : Type u} [Ring R] {M₁ M₂ M₃ : Type v}
    [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
    [Module R M₁] [Module R M₂] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃) (h : Function.Exact f g)
    [IsNoetherianRing R] [Module.Finite R M₁] [Module.Finite R M₃] :
    Module.Finite R M₂ := by
  have hk : Module.Finite R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.1 h]
    exact Module.Finite.range f
  have : IsNoetherian R M₃ := isNoetherian_of_isNoetherianRing_of_finite R M₃
  have hq : Module.Finite R (M₂ ⧸ LinearMap.ker g) :=
    Module.Finite.equiv g.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient (LinearMap.ker g)

theorem homology_finite_short_exact {R : Type u} [Ring R] {ι : Type w} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) c)} (hS : S.ShortExact) (i : ι) :
    (Finite (S.X₁.homology i) → Finite (S.X₃.homology i) → Finite (S.X₂.homology i)) ∧
    (IsNoetherianRing R → Module.Finite R (S.X₁.homology i) →
      Module.Finite R (S.X₃.homology i) → Module.Finite R (S.X₂.homology i)) := by
  have hE := hS.homology_exact₂ i
  refine ⟨fun h₁ h₃ ↦ ?_, fun _ h₁ h₃ ↦ ?_⟩
  · exact AddCommGrpCat.isFinite.prop_X₂_of_exact
      (hE.map (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) h₁ h₃
  · exact finite_middle _ _ ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hE)

end UpperTheory
