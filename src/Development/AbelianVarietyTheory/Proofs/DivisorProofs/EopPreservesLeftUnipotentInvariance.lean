module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep.UnipInv

theorem Eop_unip_left :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a r : ℕ) (f : Sm E a),
      (∀ (x : BlockIx a r → Ad E) (g : GA E a), f.1 (unip x * g) = f.1 g) →
      ∀ (τ : E →+* ℂ) (i j : Fin a) (x : BlockIx a r → Ad E) (g : GA E a),
        (Eop τ i j f).1 (unip x * g) = (Eop τ i j f).1 g := by
  intro E _ _ _ a r f hf τ i j x g
  have hc : chart f.1 (unip x * g) = chart f.1 g := by
    funext y
    unfold chart
    split_ifs
    · rw [mul_assoc, hf]
    · rfl
  have hD : ∀ X, lieD X f.1 (unip x * g) = lieD X f.1 g := fun X => by
    simp only [lieD, hc]
  simp only [Eop, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
    Pi.smul_apply, Pi.sub_apply, lieS_apply, lie_apply, hD]

end GlobalTheory.CuspRep.UnipInv
