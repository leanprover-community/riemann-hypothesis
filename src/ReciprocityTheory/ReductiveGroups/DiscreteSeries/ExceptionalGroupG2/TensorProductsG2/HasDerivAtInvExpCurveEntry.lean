module

import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HasDerivAtInvExpCurveEntry
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.CoefOfEmb
public import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IntegrableComplexContinuousBoundedSupport
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

section Mat

variable {ε : Fin n → Bool}

theorem J_mul_J_eq_one (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem unitary_group_inv_eq_conj {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g⁻¹ = Jm ε * gᴴ * Jm ε := by
  apply Matrix.inv_eq_left_inv
  unfold inUJ at hg
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg, J_mul_J_eq_one]

theorem J_conj_entry (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ) (d c : Fin n) :
    (Jm ε * A * Jm ε) d c = (if ε d then 1 else -1) * A d c * (if ε c then 1 else -1) := by
  simp [Jm, Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem J_conj_neg_mul_inv {g X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    Jm ε * (g * X)ᴴ * Jm ε = -(X * (Jm ε * gᴴ * Jm ε)) := by
  apply ReciprocityTheory.ChartRestriction.DS.J_conj_neg_mul_inv <;> assumption

theorem hasDerivAt_exp_curve_entry (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X)) c d) ((g * X) c d) 0 := by
  have h := Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 h c) d

theorem hasDerivAt_inv_exp_curve_entry {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (d c : Fin n) :
    HasDerivAt (fun t : ℝ => (g * NormedSpace.exp ((t : ℂ) • X))⁻¹ d c) (-(X * g⁻¹) d c) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inv_exp_curve_entry <;> assumption

end Mat

section Coef

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem hasDerivAt_inner_rep_exp (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (w : H) (v : D) :
    HasDerivAt (fun t : ℝ => inner ℂ w (σ (g * NormedSpace.exp ((t : ℂ) • X)) (v : H)))
      (inner ℂ w (σ g ((actM E X v : D) : H))) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_inner_rep_exp <;> assumption

def oa1Phi (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual ((g⁻¹) d c) (g c d)

def oa1DPhi (dual : Bool) (g X : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ :=
  cond dual ((-(X * g⁻¹)) d c) ((g * X) c d)

theorem hasDerivAt_tensor_phi {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool)
    (c d : Fin n) :
    HasDerivAt (fun t : ℝ => oa1Phi dual (g * NormedSpace.exp ((t : ℂ) • X)) c d) (oa1DPhi dual g X c d) 0 := by
  cases dual
  · exact hasDerivAt_exp_curve_entry g X c d
  · exact hasDerivAt_inv_exp_curve_entry hg hX d c

theorem tensor_coef_expand (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (η f : Fin n → H)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    ∑ c, inner ℂ (η c) (tensGrp dual σ g f c) = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (η c) (σ g (f d)) := by
  simp only [tensGrp, oa1Phi, inner_sum, inner_smul_right]

theorem hasDerivAt_tensor_coef (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {g X : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) (hX : inG ε X) (dual : Bool) (η : Fin n → H)
    (f : Fin n → D) :
    HasDerivAt (fun t : ℝ => ∑ c, inner ℂ (η c)
        (tensGrp dual σ (g * NormedSpace.exp ((t : ℂ) • X)) (fun d => (f d : H)) c))
      (∑ c, ∑ d, (oa1DPhi dual g X c d * inner ℂ (η c) (σ g (f d : H)) +
        oa1Phi dual g c d * inner ℂ (η c) (σ g ((actM E X (f d) : D) : H)))) 0 := by
  apply ReciprocityTheory.ChartRestriction.DS.hasDerivAt_tensor_coef <;> assumption

end Coef

section Eab

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem tensor_dphi_complex_comb (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (a b c d : Fin n) :
    oa1DPhi dual g (Formalism.REAL.cpart1 ε (Matrix.single a b 1)) c d +
        Complex.I * oa1DPhi dual g (Formalism.REAL.cpart2 ε (Matrix.single a b 1)) c d =
      cond dual (-(if d = a then (g⁻¹) b c else 0)) (if d = b then g c a else 0) := by
  apply ReciprocityTheory.ChartRestriction.DS.tensor_dphi_complex_comb <;> assumption

theorem tensor_coef_Eab_action (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (η : Fin n → H)
    (f : Fin n → D) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ c, inner ℂ (η c) (tensGrp dual σ x (fun d => (f d : H)) c)) g =
      ∑ c, inner ℂ (η c) (tensGrp dual σ g (fun d => (tensF dual E a b f d : H)) c) := by
  apply ReciprocityTheory.ChartRestriction.DS.tensor_coef_Eab_action <;> assumption

end Eab

end ReciprocityTheory.ChartRestriction.DS.G2
