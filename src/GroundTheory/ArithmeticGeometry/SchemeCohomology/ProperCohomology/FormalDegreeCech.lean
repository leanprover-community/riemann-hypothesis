module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalDegree
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesCech
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.CechFamily
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesNatural
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)
  {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a)))

omit [IsNoetherianRing A] [F.IsQuasicoherent] in
include hU in
lemma isAffineOpen_inter {m : ℕ} (t : Fin (m + 1) → ι) :
    IsAffineOpen (inter (X := X.toTopCat) 𝔘 t) := by
  rw [inter_eq_iInf]
  exact hU m t



lemma reesCoef_res {V V' : X.Opens} (hle : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV' n (resF _ (Scheme.Hom.preimage_mono _ hle) x) =
      resF F hle (reesCoef I hF hV n x) := by
  change (reesSectionsMap I hF hV' _).coeff n = resF F hle ((reesSectionsMap I hF hV x).coeff n)
  rw [← reesSectionsEquiv_apply, reesSectionsEquiv_res hle hF hV hV', reesSectionsEquiv_apply]
  rfl


lemma reesCoef_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : (reesPre I F).obj (op V)) :
    reesCoef I hF hV' n (res (reesPre I F) h x) = res (modulesAb F).obj h (reesCoef I hF hV n x) :=
  reesCoef_res I hF h hV hV' n x


lemma reesDeg_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesDeg I hF hV' n (res (reesPre I F) h x) =
      res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) := by
  apply idealPowι_app_injective I n
  have e1 : res (modulesAb (idealPow I F n)).obj h (reesDeg I hF hV n x) =
    resF (idealPow I F n) h (reesDeg I hF hV n x) := rfl
  have e2 : res (reesPre I F) h x = resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) x := rfl
  rw [e1, e2, idealPowι_reesDeg, app_resF, idealPowι_reesDeg]
  exact reesCoef_res I hF h hV hV' n x


lemma reesInc_res' {V V' : X.Opens} (h : V' ≤ V) (hV : IsAffineOpen V) (hV' : IsAffineOpen V')
    (n : ℕ) (x : Γ(idealPow I F n, V)) :
    reesInc I hF hV' n (res (modulesAb (idealPow I F n)).obj h x) =
      res (reesPre I F) h (reesInc I hF hV n x) := by
  apply reesSectionsMap_injective hF hV'
  have e1 : res (reesPre I F) h (reesInc I hF hV n x) =
    resF (reesSheaf I F) (Scheme.Hom.preimage_mono _ h) (reesInc I hF hV n x) := rfl
  have e2 : res (modulesAb (idealPow I F n)).obj h x = resF (idealPow I F n) h x := rfl
  rw [e1, e2, ← reesSectionsEquiv_apply hF hV' (resF _ _ _),
    reesSectionsEquiv_res h hF hV hV', reesSectionsEquiv_apply, reesSectionsMap_reesInc,
    reesSectionsMap_reesInc, PolynomialModule.map_lsingle, resFA_apply, app_resF]

def reesCoefFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F) (modulesAb F).obj where
  φ t := reesCoef I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesCoef_res' I hF h _ _ n x



def reesDegFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (reesPre I F)
    (modulesAb (idealPow I F n)).obj where
  φ t := reesDeg I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesDeg_res' I hF h _ _ n x



def reesIncFam (n : ℕ) : CechFamily (X := X.toTopCat) 𝔘 (modulesAb (idealPow I F n)).obj
    (reesPre I F) where
  φ t := reesInc I hF (isAffineOpen_inter 𝔘 hU t) n
  res_comm _ _ h x := reesInc_res' I hF h _ _ n x

end

end GroundTheory.Arith.SchemeCoh
