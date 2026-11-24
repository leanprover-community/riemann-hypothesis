module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.UH

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {g : ℕ}

theorem hermForm_add_left (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm, add_dotProduct]

theorem hermForm_smul_left (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm, smul_dotProduct]

theorem hermForm_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_rsmul_right (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = c * hermForm Hm z w := by
  simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul]

theorem hermForm_sub_mat (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (H₁ - H₂) z w = hermForm H₁ z w - hermForm H₂ z w := by
  simp [hermForm, Matrix.sub_mulVec, dotProduct_sub]

def imForm (Hm : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (hermForm Hm z w).im)
    (fun z z' w => by rw [hermForm_add_left, Complex.add_im])
    (fun c z w => by
      rw [show (c • z : Fin g → ℂ) = (c : ℂ) • z from by funext i; simp [Complex.real_smul],
        hermForm_smul_left, smul_eq_mul, Complex.im_ofReal_mul])
    (fun z w w' => by rw [hermForm_add_right, Complex.add_im])
    (fun c z w => by rw [hermForm_rsmul_right, smul_eq_mul]; simp)

theorem herm_eq_of_im {L : Type} [AddCommGroup L] (P : L →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ)
    (h : ∀ x y, (hermForm H₁ (P x) (P y)).im = (hermForm H₂ (P x) (P y)).im) : H₁ = H₂ := by
  have hD : ∀ x y, (hermForm (H₁ - H₂) (P x) (P y)).im = 0 := fun x y => by
    rw [hermForm_sub_mat, Complex.sub_im, h, sub_self]
  have h0 : imForm (H₁ - H₂) = 0 := by
    apply LinearMap.ext_on_range hP
    intro x
    apply LinearMap.ext_on_range hP
    intro y
    simpa [imForm] using hD x y
  have hall : ∀ z w, hermForm (H₁ - H₂) z w = 0 := by
    intro z w
    have him : ∀ z' : Fin g → ℂ, (hermForm (H₁ - H₂) z' w).im = 0 := fun z' => by
      simpa [imForm] using LinearMap.congr_fun₂ h0 z' w
    have hre := him (Complex.I • z)
    rw [hermForm_smul_left] at hre
    apply Complex.ext
    · simpa using hre
    · simpa using him z
  have hs : ∀ j : Fin g, star (Pi.single j 1 : Fin g → ℂ) = (Pi.single j 1 : Fin g → ℂ) := fun j => by
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  refine sub_eq_zero.1 ?_
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [hermForm, hs, Matrix.mulVec_single, single_dotProduct] using this

end ReciprocityTheory.ChartRestriction.G.PullbackSections.UH
