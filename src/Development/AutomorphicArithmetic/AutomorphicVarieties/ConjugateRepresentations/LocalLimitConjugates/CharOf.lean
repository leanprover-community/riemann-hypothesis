import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HomId
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.AlphaAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.HolMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.SLApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.GlNegOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.OneTmulMemCenter
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.DualIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SmSepDer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.SqOrth

section
section SlopeTestRemainingChoices
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible

private def UpperTheory.V.Cj.H.altFlip {A V M : Type} [AddCommGroup A] [Module ℝ A] [AddCommGroup V] [Module ℝ V]
    [AddCommGroup M] [Module ℝ M] {q : ℕ} (φ : A →ₗ[ℝ] (V [⋀^Fin q]→ₗ[ℝ] M)) : V [⋀^Fin q]→ₗ[ℝ] (A →ₗ[ℝ] M) where
  toFun Y :=
    { toFun := fun X => φ X Y
      map_add' := fun X X' => by rw [map_add, AlternatingMap.add_apply]
      map_smul' := fun c X => by rw [map_smul, AlternatingMap.smul_apply, RingHom.id_apply] }
  map_update_add' Y i x y := LinearMap.ext fun X => (φ X).map_update_add Y i x y
  map_update_smul' Y i c x := LinearMap.ext fun X => (φ X).map_update_smul Y i c x
  map_eq_zero_of_eq' Y _ _ h hij := LinearMap.ext fun X => (φ X).map_eq_zero_of_eq Y h hij

private theorem UpperTheory.V.Cj.H.wigner_homomorphism : UpperTheory.V.Cj.H.WigHom := by
  intro E _ _ _ a M _ _ _ _ L α z hlie hretr
  refine ⟨fun ω h0 h1 Y => ?_, fun q ω h0 h1 => ?_⟩
  · have key : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), L (toL X) (ω Y) = 0 := by
      intro X
      let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
      have hZ : star Z = -Z := by
        simp only [Z]
        rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
      have hX : toL X = toL (hp (toL X)).1 + toL Z := by
        have h : X = (hp (toL X)).1 + Z := by
          rw [hp_val]; simp only [Z]; module
        exact congrArg toL h
      have h3 := DFunLike.congr_fun h1 fun _ => hp (toL X)
      rw [dCo_apply, Fin.sum_univ_one, Subsingleton.elim (Fin.removeNth _ _) Y] at h3
      have h4 : L (toL (hp (toL X)).1) (ω Y) = 0 := by simpa using h3
      rw [congrArg L hX, map_add, LinearMap.add_apply, h4, h0 Z hZ Y]
      simp
    rw [← hretr (ω Y) 0 fun X => (key (Matrix.of X)).symm, map_zero]
  · let F : Herm E a [⋀^Fin q]→ₗ[ℝ] (Lie E a →ₗ[ℝ] M) := UpperTheory.V.Cj.H.altFlip (ω.curryLeft ∘ₗ hp)
    let ad : Matrix (Fin a) (Fin a) (Cinf E) → Lie E a →ₗ[ℝ] Lie E a := fun Y =>
      { toFun := fun X => toL (Y * Matrix.of X - Matrix.of X * Y)
        map_add' := fun X X' => by
          have h : Y * (Matrix.of X + Matrix.of X') - (Matrix.of X + Matrix.of X') * Y =
              (Y * Matrix.of X - Matrix.of X * Y) + (Y * Matrix.of X' - Matrix.of X' * Y) := by noncomm_ring
          exact congrArg toL h
        map_smul' := fun c X => by
          have h : Y * (c • Matrix.of X) - (c • Matrix.of X) * Y = c • (Y * Matrix.of X - Matrix.of X * Y) := by
            rw [smul_sub, mul_smul_comm, smul_mul_assoc]
          exact congrArg toL h }
    refine ⟨α.compAlternatingMap F, fun Y => ?_⟩
    let G : Fin (q + 1) → Lie E a →ₗ[ℝ] M := fun i =>
      (L (toL (Y i).1)).restrictScalars ℝ ∘ₗ F (i.removeNth Y) - F (i.removeNth Y) ∘ₗ ad (Y i).1
    have h3 : ∀ i, L (toL (Y i).1) (α (F (i.removeNth Y))) = α (G i) := fun i =>
      hlie _ _ _ fun X => (sub_add_cancel _ _).symm
    rw [dCo_apply, ← hretr (ω Y) (∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • G i) fun X => ?_, map_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, ← h3]
      rfl
    · rw [LinearMap.sum_apply]
      exact homId E a M L q ω h1 h0 (Matrix.of X) Y

end SlopeTestRemainingChoices

open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.wigHom :
    UpperTheory.V.Cj.H.WigHom :=
  UpperTheory.V.Cj.H.wigner_homomorphism
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] {a : ℕ}
  {N : Type} [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N]
  {N' : Type} [AddCommGroup N'] [Module ℂ N'] [Module ℝ N'] [IsScalarTower ℝ ℂ N']

omit [NumberField E] [IsScalarTower ℝ ℂ N] [IsScalarTower ℝ ℂ N'] in
private theorem hol_nat (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' : Lie E a →ₗ[ℝ] N')
    (h : ∀ X, φ (L (toL X)) = L' (toL X)) (x : Matrix (Fin a) (Fin a) ℂ) : φ (hol τ L x) = hol τ L' x := by
  simp only [hol_apply, eL, map_sum, map_smul, map_sub, h]

omit [NumberField E] [IsScalarTower ℝ ℂ N] in
private theorem hol_add (τ : E →+* ℂ) (L L' : Lie E a →ₗ[ℝ] N) : hol τ (L + L') = hol τ L + hol τ L' := by
  ext1 x
  simp only [hol_apply, eL, LinearMap.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

omit [NumberField E] in
private theorem hol_smul (τ : E →+* ℂ) (r : ℝ) (L : Lie E a →ₗ[ℝ] N) : hol τ (r • L) = (r : ℂ) • hol τ L := by
  ext1 x
  have e : ∀ v : N, r • v = (r : ℂ) • v := fun v => (algebraMap_smul ℂ r v).symm
  simp only [hol_apply, eL, LinearMap.smul_apply, Finset.smul_sum, e]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  module

variable [IsTotallyComplex E]

private theorem hol_der (τ : E →+* ℂ) (φ : N →ₗ[ℂ] N') (L : Lie E a →ₗ[ℝ] N) (L' L'' : Lie E a →ₗ[ℝ] N')
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, φ (L (toL X)) = L' (toL X) + L'' (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    φ (hol τ L x) = hol τ L' x + hol τ L'' (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  rw [hol_nat τ φ L (φ.restrictScalars ℝ ∘ₗ L) (fun _ => rfl),
    ← (holMul E a N' τ L'' (φ.restrictScalars ℝ ∘ₗ L - L')).2 Y (fun X => sub_eq_of_eq_add' (h X)) x,
    ← LinearMap.add_apply, ← hol_add, add_sub_cancel]

variable {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private theorem hol_der_end (τ : E →+* ℂ) (u : Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M)
    (Y : Matrix (Fin a) (Fin a) (Cinf E)) (h : ∀ X, u * L (toL X) - L (toL X) * u = L (toL (Y * X - X * Y)))
    (x : Matrix (Fin a) (Fin a) ℂ) :
    u * hol τ L x - hol τ L x * u = hol τ L (Y.map (coord τ) * x - x * Y.map (coord τ)) := by
  have h1 := hol_der τ (LinearMap.mulLeft ℂ u - LinearMap.mulRight ℂ u) L 0 L Y
    (fun X => (h X).trans (zero_add _).symm) x
  have h0 : hol τ (0 : Lie E a →ₗ[ℝ] Module.End ℂ M) x = 0 := by simp [hol_apply, eL]
  rw [h0, zero_add] at h1
  exact h1

end SlopeTestRemainingChoices

theorem UpperTheory.V.Cj.H.wigAlpha :
    UpperTheory.V.Cj.H.WigAlpha := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hc τ x
  have hcomm : ∀ y z, Commute (hol τ LA y) (hol τ LB z) := fun y z => by
    simp only [hol_apply, eL]
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ =>
      Commute.sum_right _ _ _ fun k _ => Commute.sum_right _ _ _ fun l _ => ?_
    exact (((((hc _ _).sub_right ((hc _ _).smul_right _)).sub_left
      (((hc _ _).sub_right ((hc _ _).smul_right _)).smul_left _)).smul_right _).smul_left _
      |>.smul_right _).smul_left _
  obtain ⟨α₀, h1, -, h3⟩ := alphaAbs M a (hol τ LA) (hol τ LB) (fun k => x - (k : ℂ)) hcomm
  set s : ℂ := (a.factorial : ℂ)⁻¹ with hs
  have e : ∀ (r : ℝ) (v : M), r • v = (r : ℂ) • v := fun r v => (algebraMap_smul ℂ r v).symm
  let α : (Lie E a →ₗ[ℝ] M) →ₗ[ℝ] M :=
    { toFun := fun f => s • α₀ (hol τ f)
      map_add' := fun f g => by rw [hol_add, map_add, smul_add]
      map_smul' := fun r f => by rw [hol_smul, map_smul, RingHom.id_apply, e, smul_comm] }
  have hα : ∀ f, α f = s • α₀ (hol τ f) := fun _ => rfl
  refine ⟨α, fun Y f f' hf => ?_, fun m f hf => ?_⟩
  · rw [hα, hα, map_smul]
    congr 1
    refine h3 _ (Y.map (coord τ)) (hol_der_end τ _ LA Y fun X => ?_) (hol_der_end τ _ LB Y fun X => ?_) _ _
      (hol_der τ _ f f' f Y hf)
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hA Y X, (hc (toL X) (toL Y)).eq]
      abel
    · rw [LinearMap.add_apply, add_mul, mul_add, ← hB Y X, (hc (toL Y) (toL X)).eq]
      abel
  · have hx : ∀ y, hol τ f y = hol τ LA y m + hol τ LB y m := fun y => by
      rw [← hol_nat τ (LinearMap.applyₗ m) (LA + LB) f (fun X => (hf _).symm), hol_add]
      rfl
    rw [hα, h1 m _ hx]
    simp only [hol_single]
    have gA := (eLRel E a _ LA hA).1 τ
    have gB := (glNegOp _ a _ ((eLRel E a _ LB hB).1 τ)).1
    rw [Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gB, show (fun i j => eL LA τ i j) = eL LA τ from rfl,
      Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet _ gA]
    have hz : (a.factorial : ℂ) ≠ 0 := by exact_mod_cast a.factorial_ne_zero
    simp only [MulOpposite.unop_smul, LinearMap.smul_apply, LinearMap.sub_apply, ← smul_sub, smul_smul]
    rw [hs, inv_mul_cancel₀ hz, one_smul]
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

namespace UpperTheory.V.Cj.H.WignerSubquotient

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private theorem relQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (S : Subalgebra ℂ (A × B)) {n : ℕ}
    (X : Fin n → Fin n → A) (Y : Fin n → Fin n → B) (h : ∀ p q, (X p q, Y p q) ∈ S) (v : ℂ) :
    (Formalism.REAL.qdet X v, Formalism.REAL.qdet Y v) ∈ S := by
  let Z : Fin n → Fin n → S := fun p q => ⟨(X p q, Y p q), h p q⟩
  have e1 : ((Formalism.REAL.qdet Z v : S) : A × B).1 = Formalism.REAL.qdet X v := mapQ ((AlgHom.fst ℂ _ _).comp S.val) Z v
  have e2 : ((Formalism.REAL.qdet Z v : S) : A × B).2 = Formalism.REAL.qdet Y v := mapQ ((AlgHom.snd ℂ _ _).comp S.val) Z v
  rw [← e1, ← e2]
  exact (Formalism.REAL.qdet Z v).2

section

variable {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

private theorem intQ {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R (Formalism.REAL.qdet X v m) = Formalism.REAL.qdet Y v (R m) := by
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M') :=
    { carrier := {z | ∀ m, R (z.1 m) = z.2 (R m)}
      mul_mem' := fun {x y} hx hy m => (hx _).trans (congrArg x.2 (hy m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S X Y h v m

private theorem intQop {k : ℕ} (R : M →ₗ[ℂ] M') (X : Fin k → Fin k → Module.End ℂ M) (Y : Fin k → Fin k → Module.End ℂ M')
    (h : ∀ p q m, R (X p q m) = Y p q (R m)) (v : ℂ) (m : M) :
    R ((Formalism.REAL.qdet (fun i j => -MulOpposite.op (X i j)) v).unop m) =
      (Formalism.REAL.qdet (fun i j => -MulOpposite.op (Y i j)) v).unop (R m) := by
  let S : Subalgebra ℂ ((Module.End ℂ M)ᵐᵒᵖ × (Module.End ℂ M')ᵐᵒᵖ) :=
    { carrier := {z | ∀ m, R (z.1.unop m) = z.2.unop (R m)}
      mul_mem' := fun {x y} hx hy m => (hy _).trans (congrArg y.2.unop (hx m))
      add_mem' := fun {x y} hx hy m => (map_add R _ _).trans (congrArg₂ (· + ·) (hx m) (hy m))
      algebraMap_mem' := fun c m => map_smul R c m }
  exact relQ S (fun i j => -MulOpposite.op (X i j)) (fun i j => -MulOpposite.op (Y i j))
    (fun p q m => (map_neg R _).trans (congrArg Neg.neg (h p q m))) v m

end

variable {E : Type} [Field E] {a : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M]

private noncomputable def res (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (N : Submodule ℂ M) (h : ∀ X, ∀ m ∈ N, L X m ∈ N) :
    Lie E a →ₗ[ℝ] Module.End ℂ N where
  toFun X := (L X).restrict (h X)
  map_add' X Y := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_add L X Y) m.1)
  map_smul' c X := LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (map_smul L c X) m.1)

private theorem res_hom {L : Lie E a →ₗ[ℝ] Module.End ℂ M} (hL : IsLieHom L) (N : Submodule ℂ M)
    (h : ∀ X, ∀ m ∈ N, L X m ∈ N) : IsLieHom (res L N h) :=
  fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hL X Y) m.1)

private theorem res_dCo {L : Lie E a →ₗ[ℝ] Module.End ℂ M} {N : Submodule ℂ M} {L' : Lie E a →ₗ[ℝ] Module.End ℂ N}
    (h : ∀ X m, (L' X m : M) = L X m) {q : ℕ} (ω' : Herm E a [⋀^Fin q]→ₗ[ℝ] N) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M)
    (hω : ∀ Y, (ω' Y : M) = ω Y) (Y : Fin (q + 1) → Herm E a) : (dCo L' ω' Y : M) = dCo L ω Y := by
  rw [dCo_apply, dCo_apply, Submodule.coe_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hω, ← h]
  exact map_zsmul N.subtype _ _

end UpperTheory.V.Cj.H.WignerSubquotient

open UpperTheory.V.Cj.H.WignerSubquotient in
theorem UpperTheory.V.Cj.H.wigSub :
    UpperTheory.V.Cj.H.WigSub := by
  intro E _ _ _ a M _ _ _ _ LA LB hA hB hAB N sA sB τ x z hz
  subst hz
  refine ⟨?_, fun q ω h1 h2 hN => ?_⟩
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a M LA LB hA hB hAB τ x
    exact (wigHom E a M (LA + LB) α _ p1 p2).1
  · obtain ⟨α, p1, p2⟩ := wigAlpha E a N (res LA N sA) (res LB N sB) (res_hom hA N sA) (res_hom hB N sB)
      (fun X Y => LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hAB X Y) m.1)) τ x
    let ω' : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] N :=
      { toFun := fun Y => ⟨ω Y, hN Y⟩
        map_update_add' := fun Y i u v => Subtype.ext (ω.map_update_add Y i u v)
        map_update_smul' := fun Y i c u => Subtype.ext (ω.map_update_smul Y i c u)
        map_eq_zero_of_eq' := fun Y i j e hij => Subtype.ext (ω.map_eq_zero_of_eq Y e hij) }
    have hL : ∀ X (m : N), ((res LA N sA + res LB N sB) X m : M) = (LA + LB) X m := fun _ _ => rfl
    obtain ⟨η, hη⟩ := (wigHom E a N (res LA N sA + res LB N sB) α _ p1 p2).2 q ω'
      (fun Z hZ Y => Subtype.ext ((h1 Z hZ Y).trans
        (Submodule.coe_sum N (fun i => ω' (Function.update Y i (brH Z hZ (Y i)))) Finset.univ).symm))
      (AlternatingMap.ext fun Y => Subtype.ext ((res_dCo hL ω' ω (fun _ => rfl) Y).trans (by rw [h2]; rfl)))
    refine ⟨(N.subtype.restrictScalars ℝ).compAlternatingMap η, fun Y => (η Y).2, fun Y => ?_⟩
    rw [← res_dCo hL η _ (fun _ => rfl) Y, hη, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub]
    exact congrArg₂ (· - ·) (intQ N.subtype _ (eL LA τ) (fun _ _ _ => rfl) x (ω' Y))
      (intQop N.subtype _ (eL LB τ) (fun _ _ _ => rfl) x (ω' Y))
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem mapQ {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] (f : A →ₐ[ℂ] B) {n : ℕ}
    (X : Fin n → Fin n → A) (u : ℂ) : f (Formalism.REAL.qdet X u) = Formalism.REAL.qdet (fun i j => f (X i j)) u := by
  simp only [Formalism.REAL.qdet, Formalism.REAL.qminor, Formalism.REAL.Tm, map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn,
    Function.comp_def, map_add, apply_ite f, AlgHom.commutes, map_zero]

private noncomputable def rAlg (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)) :=
  (Module.End.lTensorAlgHom ℂ (Fin d → ℂ) V).comp
    (Matrix.toLinAlgEquiv' : Matrix (Fin d) (Fin d) ℂ ≃ₐ[ℂ] Module.End ℂ (Fin d → ℂ)).toAlgHom

private noncomputable def rOp (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) :
    Matrix (Fin d) (Fin d) ℂ →ₐ[ℂ] (Module.End ℂ (V ⊗[ℂ] (Fin d → ℂ)))ᵐᵒᵖ where
  toFun N := MulOpposite.op (rAlg V d Nᵀ)
  map_one' := by simp
  map_mul' x y := by simp [Matrix.transpose_mul]
  map_zero' := by simp
  map_add' x y := by simp [Matrix.transpose_add]
  commutes' c := by simp [Algebra.algebraMap_eq_smul_one]

private theorem rOp_apply (V : Type) [AddCommGroup V] [Module ℂ V] (d : ℕ) (N : Matrix (Fin d) (Fin d) ℂ) :
    rOp V d N = MulOpposite.op (rAlg V d Nᵀ) := rfl

private theorem qdet_stab {M : Type} [AddCommGroup M] [Module ℂ M] (N : Submodule ℂ M) {n : ℕ}
    (X : Fin n → Fin n → Module.End ℂ M) (h : ∀ i j, ∀ m ∈ N, X i j m ∈ N) (u : ℂ) :
    ∀ m ∈ N, Formalism.REAL.qdet X u m ∈ N := by
  let S : Subalgebra ℂ (Module.End ℂ M) :=
    { carrier := {z | ∀ m ∈ N, z m ∈ N}
      mul_mem' := fun hx hy m hm => hx _ (hy m hm)
      add_mem' := fun hx hy m hm => N.add_mem (hx m hm) (hy m hm)
      algebraMap_mem' := fun c m hm => N.smul_mem c hm }
  let Z : Fin n → Fin n → S := fun i j => ⟨X i j, h i j⟩
  have e : ((Formalism.REAL.qdet Z u : S) : Module.End ℂ M) = Formalism.REAL.qdet X u := mapQ S.val Z u
  rw [← e]
  exact (Formalism.REAL.qdet Z u).2

theorem UpperTheory.V.Cj.H.capSm :
    UpperTheory.V.Cj.H.CapSm := by
  intro E _ _ _ a Ξ τ u
  have hE : ∀ i j : Fin a, Eop (a := a) τ i j = eL (N := Module.End ℂ (Sm E a)) (lie E a) τ i j := fun _ _ => rfl
  have hc : cap (a := a) τ u = Formalism.REAL.qdet (Eop (a := a) τ) (u + ((a : ℂ) - 1) / 2) := rfl
  refine ⟨?_, fun m hm => ?_, fun X => ?_, fun N hN => ?_⟩
  · let f : Module.End ℂ (Sm E a) →ₐ[ℂ] Module.End ℂ (Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
      Module.End.rTensorAlgHom ℂ (Sm E a) (Fin Ξ.d → ℂ)
    have hf : ∀ X, smA Ξ X = f (lie E a X) := fun _ => rfl
    have e : eL (smA Ξ) τ = fun i j => f (Eop (a := a) τ i j) := by
      funext i j
      simp only [hE, eL, hf, map_smul, map_sub]
    rw [e, ← mapQ, ← hc]
    rfl
  · have hd := (dualIff E a Ξ τ m).1 hm
    have hB : ∀ X, smB Ξ X = rAlg (Sm E a) Ξ.d (Ξ.dmat X) := fun X => smB_apply Ξ X
    have h := (mapQ (rOp (Sm E a) Ξ.d) (GlobalTheory.WignerGL.dualE Ξ τ) (u + ((a : ℂ) - 1) / 2)).symm.trans
      (congrArg (rOp (Sm E a) Ξ.d) (hd.2 u))
    rw [map_smul, map_one] at h
    have e : ∀ i j, rOp (Sm E a) Ξ.d (GlobalTheory.WignerGL.dualE Ξ τ i j) = -MulOpposite.op (eL (smB Ξ) τ i j) := fun i j => by
      rw [dualE_eq, map_neg, rOp_apply, Matrix.transpose_transpose]
      simp only [eL, hB, map_smul, map_sub]
    simp only [e] at h
    rw [h, MulOpposite.unop_smul, MulOpposite.unop_one]
  · rw [← UpperTheory.V.Cm.uC_capC, ← UpperTheory.V.Cm.uC_ιC]
    exact Commute.map (Subalgebra.mem_center_iff.1 (UpperTheory.V.Cm.capC_mem_center τ u) _) (UpperTheory.V.Cm.uC E a)
  · rw [hc]
    refine qdet_stab N _ (fun i j φ hφ => ?_) _
    rw [hE]
    exact N.smul_mem _ (N.sub_mem (hN _ φ hφ) (N.smul_mem _ (hN _ φ hφ)))
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem tens_map {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (N : Submodule ℂ W)
    (T : Module.End ℂ (W ⊗[ℂ] (Fin d → ℂ))) (h : ∀ φ ∈ N, ∀ v, T (φ ⊗ₜ[ℂ] v) ∈ tens d N) :
    ∀ m ∈ tens d N, T m ∈ tens d N := by
  intro m hm
  rw [← sum_cmp m, map_sum]
  exact Submodule.sum_mem _ fun i _ => h _ (mem_tens.1 hm i) _

private theorem tmul_mem {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} {N : Submodule ℂ W} {φ : W} (h : φ ∈ N)
    (v : Fin d → ℂ) : φ ⊗ₜ[ℂ] v ∈ tens d N :=
  mem_tens.2 fun i => by rw [cmp_tmul]; exact N.smul_mem _ h

theorem UpperTheory.V.Cj.H.wigSm :
    UpperTheory.V.Cj.H.WigSm := by
  intro E _ _ _ a Ξ N hN τ m hm u q ω hc hd hv
  obtain ⟨hA, hB, hAB, -, -, hI⟩ := smAB E a Ξ
  obtain ⟨c1, c2, -, -⟩ := capSm E a Ξ τ u
  have hs : smA Ξ + smB Ξ = smLie Ξ := LinearMap.ext fun X => by
    rw [LinearMap.add_apply, smA_apply, smB_apply]; rfl
  have key := wigSub E a _ (smA Ξ) (smB Ξ) hA hB hAB (tens Ξ.d N)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smA_apply, LinearMap.rTensor_tmul]; exact tmul_mem (hN X φ hφ) _)
    (fun X => tens_map N _ fun φ hφ v => by
      rw [smB_apply, LinearMap.lTensor_tmul]; exact tmul_mem hφ _)
    τ (u + ((a : ℂ) - 1) / 2)
    ((cap τ u - (m.map (u + ·)).prod • (1 : Module.End ℂ (Sm E a))).rTensor (Fin Ξ.d → ℂ)) (by
      rw [c1, c2 m hm, LinearMap.rTensor_sub, LinearMap.rTensor_smul]
      congr 2
      exact LinearMap.rTensor_id _ _)
  rw [hs] at key
  cases q with
  | zero =>
    show app _ ω = 0
    refine AlternatingMap.ext fun Y => ?_
    exact key.1 ω (hI _ ω hc) hd Y
  | succ q =>
    obtain ⟨η, h1, h2⟩ := key.2 q ω (hI _ ω hc) hd (fun Y => mem_tens.2 (hv Y))
    exact ⟨η, fun X => mem_tens.1 (h1 X), AlternatingMap.ext fun Y => h2 Y⟩
end

section
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (T : Module.End ℂ W) (i : Fin d)
    (x : W ⊗[ℂ] (Fin d → ℂ)) : cmp i (T.rTensor _ x) = T (cmp i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v => simp

private theorem adj_rT {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) (X : GlobalTheory.CuspRep.Lie E a)
    (x : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)) : smAdj Ξ r X (T.rTensor _ x) = T.rTensor _ (smAdj Ξ r X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul φ v =>
    simp only [smAdj, adj_apply, smA_apply, smB_apply, map_sub, LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, hT,
      LinearMap.map_smul_of_tower]

private theorem cocl_app {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (Ξ : AlgRep E a) (r : ℝ)
    {n : ℕ} (e : Fin n → Herm E a)
    (T : Module.End ℂ (Sm E a)) (hT : ∀ X φ, lie E a X (T φ) = T (lie E a X φ)) :
    ∀ {q : ℕ} (ω : Co Ξ q), Coclosed (smAdj Ξ r) e ω → Coclosed (smAdj Ξ r) e (app T ω)
  | 0, _, _ => trivial
  | _ + 1, ω, h => by
    have h' : del (smAdj Ξ r) e ω = 0 := h
    show del (smAdj Ξ r) e (app T ω) = 0
    refine AlternatingMap.ext fun X => ?_
    have h2 := congrArg (fun η => T.rTensor (Fin Ξ.d → ℂ) (η X)) h'
    simp only [del_apply, map_sum, AlternatingMap.zero_apply, map_zero] at h2
    simp only [del_apply, app_apply, adj_rT Ξ r T hT, AlternatingMap.zero_apply, h2]

theorem UpperTheory.V.Cj.H.charOf :
    UpperTheory.V.Cj.H.CharOf := by
  intro E _ _ _ a ha n e he Ξ r m hm q ω h1 h2 h3 h4 X i t u
  have hL := (sqLie E a r).2
  obtain ⟨-, -, c3, c4⟩ := capSm E a Ξ t u
  have hx := wigSm E a Ξ (sqSub E a r) hL t (m t) (hm t) u q ω h1 h2 h4
  have hv : Val (sqSub E a r) (app (cap t u - ((m t).map (u + ·)).prod • 1) ω) := fun Y j => by
    rw [app_apply, cmp_rT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Submodule.sub_mem _ (c4 _ hL _ (h4 Y j)) (Submodule.smul_mem _ _ (h4 Y j))
  have hc := cocl_app Ξ r e (cap t u - ((m t).map (u + ·)).prod • 1) (fun Y φ => by
    have := LinearMap.congr_fun (c3 Y).eq φ
    simp only [Module.End.mul_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, this]) ω h3
  have h0 := (sqOrth E a ha n e he Ξ r q).1 _ hv hc hx
  have h5 := congrArg (fun η : Co Ξ q => cmp i (η X)) h0
  simp only [app_apply, cmp_rT, AlternatingMap.zero_apply, map_zero, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at h5
  exact sub_eq_zero.1 h5
end
