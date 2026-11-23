module

public import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq

theorem LeafBZ_of : LeafBZ := by
  intro R _ K X U n W a ⟨b, hb0, hba⟩
  subst hba
  refine ⟨?_, ?_⟩
  · show ((K.X n).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    have e := congrArg (fun φ => φ.hom b) ((K.d (n - 1) n).hom.naturality (W.ι ⁻¹ᵁ U).ι.op)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
    rw [← e]
    have hb0' : ((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom b = 0 := hb0
    rw [hb0', map_zero]
  · show ((K.d n (n + 1)).hom.app (op W.toScheme)).hom (((K.d (n - 1) n).hom.app (op W.toScheme)).hom b) = 0
    change ((K.d (n - 1) n ≫ K.d n (n + 1)).hom.app (op W.toScheme)).hom b = 0
    rw [K.d_comp_d]
    rfl

end LateralTheory.CohomologicalPurity.Cl.Flq
