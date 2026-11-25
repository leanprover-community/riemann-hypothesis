module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPeriodPairIdealCurveLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeCovolumePosAndSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI
import Mathlib.RingTheory.PiTensorProduct
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.RatEquiv

variable {D : D7}

theorem hf_add_left (T : Tor D) {N N' : ℕ} (x y z : VC D N N') : Hf D T (x + y) z = Hf D T x z + Hf D T y z := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem hf_add_right (T : Tor D) {N N' : ℕ} (x y z : VC D N N') : Hf D T x (y + z) = Hf D T x y + Hf D T x z := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem U_U (T : Tor D) {N N' : ℕ} (x a : VC D N N') (c : ℂ) (G : VC D N N' → ℂ) (z : VC D N N') :
    U D T x (fun w => c * U D T a G w) z =
      c * Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2) * U D T (x + a) G z := by
  simp only [U, add_assoc]
  have : ∀ a b e g u : ℂ, a + b = e + g →
      c * (u * Complex.exp a) * Complex.exp b = c * Complex.exp e * (u * Complex.exp g) := by
    intro a b e g u hh
    calc _ = c * u * Complex.exp (a + b) := by simp only [Complex.exp_add]; ring
      _ = _ := by rw [hh]; simp only [Complex.exp_add]; ring
  apply this
  simp only [hf_add_left, hf_add_right]
  ring

theorem term_indep (T : Tor D) {N N' : ℕ} {A B : AddSubgroup (VC D N N')} {G H : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) (hH : H ∈ ThSp D T B) (h0 : H ≠ 0) {x a : VC D N N'} (hx : x ∈ B) (haB : a ∈ B)
    (haA : a ∈ A) (z : VC D N N') :
    al D T (x + a) * U D T (x + a) G z = al D T x * U D T x G z := by
  have key : ∀ F : VC D N N' → ℂ, (∀ w, al D T a * U D T a F w = F w) → ∀ w, U D T x F w =
      al D T a * Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2) * U D T (x + a) F w := by
    intro F hF w
    rw [← U_U]
    congr 1
    exact (funext hF).symm
  obtain ⟨w, hw⟩ := Function.ne_iff.1 h0
  have h1 := hH.2 x hx w
  have h2 := hH.2 _ (B.add_mem hx haB) w
  rw [key H (hH.2 a haB)] at h1
  have h3 : U D T (x + a) H w ≠ 0 := by
    intro h
    rw [h, mul_zero] at h2
    exact hw h2.symm
  have h4 : al D T (x + a) = al D T x * (al D T a *
      Complex.exp ((Real.pi : ℂ) * (Hf D T a x - Hf D T x a) / 2)) :=
    mul_right_cancel₀ h3 (by rw [h2, mul_assoc, h1])
  rw [key G (hG.2 a haA), h4]
  ring

theorem iop_transport (T : Tor D) {N N' : ℕ} (φ : VC D N N' ≃+ VC D N N')
    (hφ : ∀ x y, Hf D T (φ x) (φ y) = Hf D T x y) {A B A' B' : AddSubgroup (VC D N N')}
    (hA : ∀ x, φ x ∈ A' ↔ x ∈ A) (hB : ∀ x, φ x ∈ B' ↔ x ∈ B) {G H : VC D N N' → ℂ}
    (hG : G ∈ ThSp D T A) (hH : H ∈ ThSp D T B) (h0 : H ≠ 0) (z : VC D N N') :
    Iop D T A' B' (fun w => G (φ.symm w)) (φ z) = Iop D T A B G z := by
  let e : B ≃+ B' :=
    { toFun := fun x => ⟨φ x, (hB _).2 x.2⟩
      invFun := fun y => ⟨φ.symm y, (hB _).1 (by simpa using y.2)⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      map_add' := fun x y => by simp }
  have he : (A.addSubgroupOf B).map e.toAddMonoidHom = A'.addSubgroupOf B' := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [AddSubgroup.mem_addSubgroupOf]
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := e.injective h
      subst this
      exact (hA _).2 hx'
    · intro h
      exact ⟨x, (hA _).1 h, rfl⟩
  let ε := QuotientAddGroup.congr _ _ e he
  have hi : (A'.addSubgroupOf B').index = (A.addSubgroupOf B).index := (Nat.card_congr ε.toEquiv).symm
  have ht : ∀ x, al D T (φ x) * U D T (φ x) (fun w => G (φ.symm w)) (φ z) = al D T x * U D T x G z := by
    intro x
    simp only [al, U, hφ, ← map_add (f := _), AddEquiv.symm_apply_apply]
  unfold Iop
  rw [hi]
  congr 1
  symm
  refine finsum_eq_of_bijective ε ε.bijective fun q => ?_
  obtain ⟨y, hy⟩ := e.surjective (ε q).out
  have h1 : (y : B ⧸ A.addSubgroupOf B) = q := by
    apply ε.injective
    rw [← QuotientAddGroup.out_eq' (ε q), ← hy]
    rfl
  have h2 : -(q.out) + y ∈ A.addSubgroupOf B := by
    rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq', h1]
  rw [← hy]
  change _ = al D T (φ y) * U D T (φ y) (fun w => G (φ.symm w)) (φ z)
  rw [ht, ← term_indep T hG hH h0 q.out.2 (-(q.out) + y).2 h2]
  simp

section Scalar

variable {N N' : ℕ} {s : D.host.E} (hs : s * D.host.conj s = 1) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)

theorem closure_iff {V : Type} [AddCommGroup V] (φ : V ≃+ V) {S S' : Set V}
    (h1 : ∀ x ∈ S, φ x ∈ AddSubgroup.closure S') (h2 : ∀ y ∈ S', φ.symm y ∈ AddSubgroup.closure S) (x : V) :
    φ x ∈ AddSubgroup.closure S' ↔ x ∈ AddSubgroup.closure S := by
  have a : AddSubgroup.closure S ≤ (AddSubgroup.closure S').comap (φ : V →+ V) :=
    (AddSubgroup.closure_le _).2 h1
  have b : AddSubgroup.closure S' ≤ (AddSubgroup.closure S).comap (φ.symm : V →+ V) :=
    (AddSubgroup.closure_le _).2 h2
  exact ⟨fun h => by simpa using b h, fun h => a h⟩

end Scalar

theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z :=
  _root_.GlobalTheory.HalfPeriodTheta.theta_signed_translation

theorem Iop_smul (T : Tor D) {N N' : ℕ} (A₁ A₂ : AddSubgroup (VC D N N')) (c : ℂ) (G : VC D N N' → ℂ) :
    Iop D T A₁ A₂ (fun z => c * G z) = fun z => c * Iop D T A₁ A₂ G z := by
  funext z
  simp only [Iop, U]
  rw [mul_left_comm c]
  congr 1
  rw [mul_finsum]
  congr 1; funext q; ring

end GlobalTheory.RatEquiv
