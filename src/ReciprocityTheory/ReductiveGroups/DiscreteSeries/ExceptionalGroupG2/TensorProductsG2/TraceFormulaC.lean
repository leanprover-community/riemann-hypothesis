module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormulaC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.TraceFormulaA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefEmbed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SigLamMemLpOfNe
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothA

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev tfL2n (ε : Fin n → Bool) : Type := PiLp 2 (fun _ : Fin n => L2 ε)

def tfRdiag (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => rreg ε g ∘L ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfRdiag_apply (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) (c : Fin n) :
    tfRdiag ε g v c = rreg ε g (v c) := rfl

theorem vectorL2_ext {ε : Fin n → Bool} {v w : tfL2n ε} (h : ∀ c, v c = w c) : v = w := by
  apply WithLp.ofLp_injective
  funext c
  exact h c

theorem tfRdiag_isURepOn (ε : Fin n → Bool) : IsURepOn (UJset ε) (tfRdiag ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.tfRdiag_isURepOn <;> assumption

theorem tfRdiag_smooth {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) :
    v ∈ smD ε (tfRdiag ε) := by
  apply ReciprocityTheory.ChartRestriction.DS.tfRdiag_smooth <;> assumption

theorem tfRdiag_hasDerivAt {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    HasDerivAt (fun t : ℝ => tfRdiag ε (NormedSpace.exp ((t : ℂ) • X)) v)
      (WithLp.toLp 2 (fun c => dS (rreg ε) X (v c))) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.tfRdiag_hasDerivAt <;> assumption

theorem tfRdiag_dS {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (c : Fin n) :
    dS (tfRdiag ε) X v c = dS (rreg ε) X (v c) := by
  have h := (tfRdiag_hasDerivAt hv hX).deriv
  have h2 := congrArg (fun w : tfL2n ε => w c) h
  exact h2

theorem tfRdiag_smE {ε : Fin n → Bool} {v : tfL2n ε} (hv : ∀ c, v c ∈ smD ε (rreg ε)) (a b c : Fin n) :
    ((smE ε (tfRdiag ε) a b ⟨v, tfRdiag_smooth hv⟩ : smD ε (tfRdiag ε)) : tfL2n ε) c =
      ((smE ε (rreg ε) a b ⟨v c, hv c⟩ : smD ε (rreg ε)) : L2 ε) := by
  rw [smE_apply (tfRdiag_isURepOn ε), smE_apply (rreg_isURepOn ε)]
  simp only [PiLp.add_apply, PiLp.smul_apply]
  rw [tfRdiag_dS hv (SmDerA.inG_cpart1 ε _), tfRdiag_dS hv (SmDerA.inG_cpart2 ε _)]

def tfJ (ε : Fin n → Bool) : tfL2n ε →L[ℂ] tfL2n ε :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).symm.toContinuousLinearMap ∘L
    (ContinuousLinearMap.pi fun c => tfSgn ε c • ContinuousLinearMap.proj c) ∘L
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => L2 ε)).toContinuousLinearMap

theorem tfJ_apply (ε : Fin n → Bool) (v : tfL2n ε) (c : Fin n) : tfJ ε v c = tfSgn ε c • v c := rfl

theorem tfRdiag_tfJ (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (v : tfL2n ε) :
    tfRdiag ε g (tfJ ε v) = tfJ ε (tfRdiag ε g v) :=
  vectorL2_ext fun c => by rw [tfRdiag_apply, tfJ_apply, tfJ_apply, tfRdiag_apply, map_smul]

theorem toL2_congr_of_eq_on_UJset {ε : Fin n → Bool} {F F' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = F' g) : toL2 ε F = toL2 ε F' := by
  apply ReciprocityTheory.ChartRestriction.DS.toL2_congr_of_eq_on_UJset <;> assumption

section Ph

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def tfPh (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) : tfL2n ε :=
  WithLp.toLp 2 (fun c => toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ))

theorem tfPh_apply (dual : Bool) (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (y : H)
    (ζ : Fin n → H) (c : Fin n) :
    tfPh dual ε σ y ζ c = toL2 ε (coefMap dual σ (Pi.single c (tfSgn ε c • y)) ζ) := rfl

end Ph

end ReciprocityTheory.ChartRestriction.DS.G2
