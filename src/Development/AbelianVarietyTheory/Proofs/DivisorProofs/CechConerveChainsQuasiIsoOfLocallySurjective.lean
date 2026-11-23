module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveMapEqCechNerveOfPreservesWidePushoutsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoChainsCechOfIsLocallySurjectiveStatement
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_cech_conerve_quasiIso : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  intro R _ T _ _ Ψ hΨ U V g hg
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts T Ψ hΨ U V g
  have h2 := GlobalTheory.T.quasiIso_chains_cech_of_isLocallySurjective' R _ _ (Ψ.map g).unop hg
  let h : ((Arrow.mk (Ψ.map g).unop).cechNerve : Spc) ⟶ disc.obj (Ψ.obj U).unop :=
    (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
  have key : lev Ψ (coAug g) = e ≫ h := hc.symm
  have h2' : QuasiIso ((chains R).map h) := h2
  rw [key, Functor.map_comp]
  haveI : IsIso ((chains R).map e) := inferInstance
  exact quasiIso_comp _ _
end GlobalTheory.EtC
