module

public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjDehom
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.StalkLoc
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

namespace AffPres

variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)} (P : AffPres s)

theorem secHom_surj : Function.Surjective P.secHom := by
  intro t
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin P.n) ℂ ⧸ P.K))).hom (P.iso.inv.appTop (P.V.topIso.inv t)))
  refine ⟨a, ?_⟩
  show P.V.topIso.hom (P.iso.hom.appTop ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk P.K a))) = t
  rw [ha, ← CommRingCat.comp_apply (Scheme.ΓSpecIso _).hom, Iso.hom_inv_id, CommRingCat.id_apply,
    ← CommRingCat.comp_apply P.iso.inv.appTop, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id,
    Scheme.Hom.id_appTop, CommRingCat.id_apply, ← CommRingCat.comp_apply P.V.topIso.inv, Iso.inv_hom_id,
    CommRingCat.id_apply]

theorem isAffineOpen_V' : IsAffineOpen P.V := by
  have : IsAffine P.V.toScheme := IsAffine.of_isIso P.iso.hom
  exact this

end AffPres

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)

theorem eval_val_chartCoord (p : (k : K) → ι k) (y : projX P hP) (hy : y ∈ (chartOpen hP p).1)
    (hc : IsClosed ({y} : Set (projX P hP))) (f : MvPolynomial (Σ k, ι k) ℂ) :
    eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy) f =
      val (toSpecC hP) ((gammaChart hP p).symm (Ideal.Quotient.mk _ f)) y hy := by
  obtain ⟨φ, hφ⟩ := val_ringHom (toSpecC hP) (chartOpen hP p).1 y hy hc
  have h := MvPolynomial.ringHom_ext
    (f := eval (fun q => val (toSpecC hP) (chartCoord hP p q) y hy))
    (g := φ.comp ((gammaChart hP p).symm.toRingHom.comp (Ideal.Quotient.mk (chartIdeal P p)))) ?_ ?_
  · exact (RingHom.congr_fun h f).trans (hφ _)
  · intro a
    rw [eval_C, RingHom.comp_apply, RingHom.comp_apply, hφ]
    show a = val _ ((gammaChart hP p).symm (Ideal.Quotient.mk _ (C a))) y hy
    rw [gammaChart_symm_C, val_const _ _ y hy hc]
  · intro q
    rw [eval_X, RingHom.comp_apply, RingHom.comp_apply, hφ]
    rfl

end

end ReciprocityTheory.AnForm.R
