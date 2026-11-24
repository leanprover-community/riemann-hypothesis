module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemi
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open UpperTheory.Gal.CertificateRingHomMap (wop wmul wmap)

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem conv_conj (σ : ℂ ≃+* ℂ) {H : Type} [Group H] (K : Subgroup H) (f₁ f₂ : H → ℂ) :
    Formalism.UG.conv K (fun g => σ (f₁ g)) (fun g => σ (f₂ g)) = fun g => σ (Formalism.UG.conv K f₁ f₂ g) := by
  funext g
  unfold Formalism.UG.conv
  have h := σ.toAddEquiv.map_finsum
    (fun x : H ⧸ K => f₁ (Quotient.out x) * f₂ ((Quotient.out x)⁻¹ * g))
  simpa [map_mul] using h.symm

private theorem wordFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (w : List J) :
    wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g)) = fun g => σ (wordFn K ψ w f g) := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    show Formalism.UG.conv K (fun g => σ (ψ j g)) (wordFn K (fun j g => σ (ψ j g)) w (fun g => σ (f g))) = _
    rw [ih, conv_conj]
    rfl

private theorem polyFn_conj (σ : ℂ ≃+* ℂ) {H J : Type} [Group H] (K : Subgroup H) (ψ : J → H → ℂ) (f : H → ℂ)
    (s : List J →₀ ℂ) :
    polyFn K (fun j g => σ (ψ j g)) (wmap σ.toRingHom s) (fun g => σ (f g)) = fun g => σ (polyFn K ψ s f g) := by
  funext g
  unfold polyFn wmap
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]

  simp [Finsupp.sum, Finset.sum_apply, map_sum, wordFn_conj]

private theorem wmap_wmul {J : Type} (f : ℂ →+* ℂ) (a s : List J →₀ ℂ) :
    wmap f (wmul a s) = wmul (wmap f a) (wmap f s) := by
  unfold wmul wmap
  have hm : ∀ t : List J →₀ ℂ, Finsupp.mapRange f f.map_zero t =
      Finsupp.mapRange.addMonoidHom f.toAddMonoidHom t := fun t => rfl
  rw [Finsupp.sum_mapRange_index (by intro w; simp)]
  rw [hm, map_finsuppSum]
  refine Finsupp.sum_congr (fun w _ => ?_)
  rw [map_finsuppSum, Finsupp.sum_mapRange_index (by intro w'; simp)]
  refine Finsupp.sum_congr (fun w' _ => ?_)
  rw [Finsupp.mapRange.addMonoidHom_apply, Finsupp.mapRange_single]
  congr 1
  exact map_mul f (a w) (s w')

theorem polyFnConj_of : PolyFnConj := fun σ _ _ _ K ψ f =>
  ⟨wordFn_conj σ K ψ f, polyFn_conj σ K ψ f, wmap_wmul σ.toRingHom⟩

end UpperTheory.Gal.LocalSmoothExtension

end
