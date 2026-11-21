import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by
  simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

theorem herm_expand {O : Type} [CommRing O] (bar : O →+* O) {M : Type} [AddCommGroup M] [Module O M]
    (h : M → M → O) (hadd : ∀ m m' n, h (m + m') n = h m n + h m' n)
    (hsmul : ∀ (c : O) m n, h (c • m) n = c * h m n) (hsym : ∀ m n, h n m = bar (h m n))
    (P : Summand O M) (m n : M) :
    h m n = ∑ i, ∑ j, P.incl m i * bar (P.incl n j) *
      h (P.proj (Pi.single i 1)) (P.proj (Pi.single j 1)) := by
  have hx : ∀ m : M, m = ∑ i, P.incl m i • P.proj (Pi.single i 1) := fun m => by
    have e : P.proj (P.incl m) = m := congr($(P.proj_incl) m)
    simp only [← map_smul, ← map_sum]
    rw [← pi_eq_sum_univ', e]
  have lin : ∀ m n : M, h m n = ∑ i, P.incl m i * h (P.proj (Pi.single i 1)) n := fun m n => by
    let f : M →+ O := AddMonoidHom.mk' (fun m => h m n) fun a b => hadd a b n
    have : f m = f (∑ i, P.incl m i • P.proj (Pi.single i 1)) := congrArg f (hx m)
    rw [map_sum] at this
    exact this.trans (Finset.sum_congr rfl fun i _ => hsmul _ _ _)
  rw [lin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsym n, lin n, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← hsym, _root_.mul_assoc]


end GlobalTheory.HermTensorLB
