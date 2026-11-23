module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp)

namespace LateralTheory.EWeil.StabPf

section Proj
variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) {X : Scheme.{0}} (p : X ⟶ Sp K)

def proj : geom Ω p ⟶ geom L p :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (algebraMap L Ω))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3)

theorem galMap_proj (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ L.fixingSubgroup) : galMap Ω p σ ≫ proj L p = proj L p := by
  apply pullback.hom_ext
  · simp only [proj, Category.assoc, pullback.lift_fst, galMap_fst]
  · simp only [proj, Category.assoc, pullback.lift_snd]
    rw [galMap_snd_assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact (mem_fixingSubgroup_iff _).1 hσ x x.2

end Proj

end LateralTheory.EWeil.StabPf
