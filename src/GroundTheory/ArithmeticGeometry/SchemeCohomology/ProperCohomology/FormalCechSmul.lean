module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalDegreeCech
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits

universe u

noncomputable section

attribute [local instance] algebraOfOver

section Sum

variable {T : TopCat.{u}} {ι : Type u} (𝔘 : ι → Opens T) {P : (Opens T)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {p : ℕ}

lemma cls_sum {α : Type*} (s : Finset α) (f : α → Cochain P 𝔘 p) (hf : ∀ a, d P 𝔘 p (f a) = 0)
    (h : d P 𝔘 p (∑ a ∈ s, f a) = 0) : cls (∑ a ∈ s, f a) h = ∑ a ∈ s, cls (f a) (hf a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    conv_rhs => rw [Finset.sum_empty]
    exact (cls_congr 𝔘 (Finset.sum_empty) h (map_zero _)).trans cls_zero
  | insert a s ha ih =>
    have hs : d P 𝔘 p (∑ b ∈ s, f b) = 0 := by

      rw [map_sum]
      exact Finset.sum_eq_zero fun b _ => hf b
    conv_rhs => rw [Finset.sum_insert ha, ← ih hs]
    exact (cls_congr 𝔘 (Finset.sum_insert ha) h (by rw [map_add (f := _), hf a, hs, add_zero])).trans
      (cls_add _ _ (hf a) hs _)

end Sum

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  [X.Over (Spec (.of A))] {F : X.Modules} [F.IsQuasicoherent] (hF : IsCoherent F)

lemma reesCoef_reesInr_smul {V : X.Opens} (hV : IsAffineOpen V) (r : reesAlgebra I) (N : ℕ)
    (s : Γ(reesSheaf I F, reesPr I X ⁻¹ᵁ V)) :
    reesCoef I hF hV N (reesInr I V r • s) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N, ((r : Polynomial A).coeff ij.1) • reesCoef I hF hV ij.2 s := by
  change (reesSectionsMap I hF hV (reesInr I V r • s)).coeff N = _
  rw [reesSectionsMap_smul]
  exact PolynomialModule.smul_apply (r : Polynomial A) (reesSectionsMap I hF hV s) N

variable {ι : Type u} (𝔘 : ι → X.Opens)
  (hU : ∀ (m : ℕ) (t : Fin (m + 1) → ι), IsAffineOpen (⨅ a, 𝔘 (t a))) (p : ℕ)



lemma reesCoefFam_reesMul (r : reesAlgebra I) (N : ℕ) (x : cechH (reesPre I F) 𝔘 p) :
    (reesCoefFam I hF 𝔘 hU N).cechH p (cechHMap 𝔘 (modulesAbMap (reesMul I F r)).hom p x) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal N,
        ((r : Polynomial A).coeff ij.1) • (reesCoefFam I hF 𝔘 hU ij.2).cechH p x := by
  obtain ⟨σ, hσ, rfl⟩ := exists_cls x
  have hterm : ∀ ij : ℕ × ℕ, ((r : Polynomial A).coeff ij.1) •
      (reesCoefFam I hF 𝔘 hU ij.2).cechH p (cls σ hσ) =
      cls (push 𝔘 (smulAbRingHom F (algebraMap A Γ(X, ⊤) ((r : Polynomial A).coeff ij.1))).asHom.hom p
        ((reesCoefFam I hF 𝔘 hU ij.2).cochain p σ))
        (by rw [← push_d, ← CechFamily.cochain_d, hσ, map_zero, map_zero]) := fun ij => rfl
  rw [Finset.sum_congr rfl (fun ij _ => hterm ij), ← cls_sum]
  · rw [cechHMap_cls, CechFamily.cechH_cls]
    refine cls_congr 𝔘 (funext fun t => ?_) _ _
    rw [Finset.sum_apply]
    exact reesCoef_reesInr_smul I hF (isAffineOpen_inter 𝔘 hU t) r N (σ t)
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun ij _ => by
      rw [← push_d, ← CechFamily.cochain_d, hσ, map_zero, map_zero]

end

end GroundTheory.Arith.SchemeCoh
