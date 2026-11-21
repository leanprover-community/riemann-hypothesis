import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.DimEqZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomFromSpecResidueField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme

section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.MulPullAny

open GlobalTheory.MulPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem iso_of_hasGen {X : Scheme.{0}} {L : LB X} {F : X ⟶ X} {m : ℤ}
    (h : HasGen L (K := Fin 2) ![F, 𝟙 X] ![1, -m]) :
    ∃ w : LB.Iso (AbLaw.pw L m) (L.pull F), w.IsGen := by
  obtain ⟨t, ht⟩ := h
  have le : ∀ p : (PUnit → L.ι) × L.ι, (L.pull F).U p.1 ⊓ L.U p.2 ≤
      LB.wchart L ![F, 𝟙 X] ![p.1 PUnit.unit, p.2] := fun p y hy => Set.mem_iInter.2 fun k => by
    fin_cases k
    exacts [mem_pull.1 hy.1, hy.2]
  refine ⟨⟨fun p => res (le p) (t.s ![p.1 PUnit.unit, p.2])⟩, (isGen_iff _).2 ?_⟩
  intro Y f y j j' k k' hj hj' hk hk'
  have m₁ : f y ∈ (L.pull F).U (fun _ => j) ⊓ L.U k := ⟨mem_pull.2 hj, hk⟩
  have m₂ : f y ∈ (L.pull F).U (fun _ => j') ⊓ L.U k' := ⟨mem_pull.2 hj', hk'⟩
  refine (gm_res f y (le (fun _ => j, k)) m₁ _).trans
    ((gen_trans ht f y (le (fun _ => j, k) m₁) (le (fun _ => j', k') m₂)).trans
      (congrArg₂ (· * ·) ?_ (gm_res f y (le (fun _ => j', k')) m₂ _).symm))
  rw [trF, Fin.prod_univ_two]
  simp only [Category.comp_id, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg]
  exact congrArg (fun u => _ * u⁻¹) (map_zpow (gm f y (L.U k ⊓ L.U k')) (L.g k k') m).symm

theorem mulPull_of_symm : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ H : LB B.left, H.IsLB → (∃ w : LB.Iso H (H.pull (GrpObj.inv : B ⟶ B).left), w.IsGen) → ∀ n : ℕ, ∃ w : LB.Iso (pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (mulA B n).left), w.IsGen := by
  intro K _ _ B _ hB H hH ⟨w, hw⟩ n
  have := hB.comm
  have hcube : HasGen H (thφ B (x3 B)) thε := GlobalTheory.exists_gen_theta_of_isAbelianScheme K B hB H hH
  have hrig : HasGen H (K := PUnit) (fun _ => eSec B) (fun _ => 1) :=
    DVR.exists_gen_of_local (V := K) H hH _ _
  have hneg : HasGen H (K := Fin 2) ![𝟙 B.left ≫ (GrpObj.inv : B ⟶ B).left, 𝟙 B.left] ![1, -1] :=
    Geo.Tor.gen_of_iso ((Geo.Tor.isGen_iff w).1 hw) _
  have main : HasGen H (K := Fin 2) ![(𝟙 B : B ⟶ B).left, ((𝟙 B : B ⟶ B) ^ n).left] ![(n : ℤ) ^ 2, -1] := by
    refine hasGen_pow hH hcube (𝟙 B) ?_ ?_ n
    · refine (hrig.pull (toUnit B).left).of_formEq hH (fun U _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine hneg.inv.of_formEq hH (fun U _ h => ?_)
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        neg_neg, _root_.mul_one]
      exact _root_.mul_comm _ _
  refine iso_of_hasGen (main.inv.of_formEq hH (fun U _ h => ?_))
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    neg_neg, _root_.mul_one, Nat.cast_pow]
  exact _root_.mul_comm _ _

end GlobalTheory.MulPullAny
end
end

section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.MulFiniteAny

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pw_one {X : Scheme.{0}} (H : LB X) : pw H ((1 : ℕ) : ℤ) = H := by
  cases H
  simp [AbLaw.pw]

theorem relAmple_of_veryAmpleBy' {R : Type} [CommRing R] {A : Over (Spec (CommRingCat.of R))}
    {L : LB A.left} (hL : L.IsLB) {M : ℕ} (s : Fin (M + 1) → LB.Sec L)
    (hA : VeryAmpleBy A.hom L s) : RelAmple A L := by
  have h : ∀ (s : Fin (M + 1) → LB.Sec (pw L ((1 : ℕ) : ℤ))),
      VeryAmpleBy A.hom (pw L ((1 : ℕ) : ℤ)) s → RelAmple A L :=
    fun s hs => GlobalTheory.Unif.relAmple_of_veryAmpleBy hL le_rfl s hs
  rw [pw_one] at h
  exact h s hA

theorem mul_eq_one_of_covolume_identity {G : Type} [CommGroup G] (a b c : G) :
    a * b ^ (-1 : ℤ) * c⁻¹ = (b * a⁻¹ * c)⁻¹ := by
  simp only [mul_inv, inv_inv, zpow_neg, zpow_one]
  rw [_root_.mul_comm a]

theorem exists_gen {X : Scheme.{0}} (L : LB X) (m : X ⟶ X) (e : ℤ)
    (w : LB.Iso (pw L e) (L.pull m)) (hw : w.IsGen) :
    ∃ α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![e, -1]), α.IsGen := by
  have le : ∀ j : Fin 2 → L.ι, LB.wchart L (K := Fin 2) ![𝟙 X, m] j ≤
      (L.pull m).U (fun _ => j 1) ⊓ (pw L e).U (j 0) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1, Set.mem_iInter.1 hy 0⟩
  refine ⟨⟨fun j => (res (le j) (w.s (fun _ => j 1, j 0)))⁻¹⟩, fun p q => unit_ext fun y hy => ?_⟩
  have val : ∀ p : Fin 2 → L.ι, y ∈ LB.wchart L (K := Fin 2) ![𝟙 X, m] p →
      gm (𝟙 X) y _ (res (le p) (w.s (fun _ => p 1, p 0)))⁻¹ =
        (gm (𝟙 X) y ((L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0)) (w.s (fun _ => p 1, p 0)))⁻¹ :=
    fun p hp => (map_inv _ _).trans (congrArg (·⁻¹) (gm_res (𝟙 X) y (le p) hp _))
  have hm : (𝟙 X : X ⟶ X) y ∈ (L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0) ⊓
      ((L.pull m).U (fun _ => q 1) ⊓ (pw L e).U (q 0)) := ⟨le p hy.1, le q hy.2⟩
  have e₀ := congrArg (gm (𝟙 X) y ((L.pull m).U (fun _ => p 1) ⊓ (pw L e).U (p 0) ⊓
      ((L.pull m).U (fun _ => q 1) ⊓ (pw L e).U (q 0))))
    (hw (fun _ => p 1, p 0) (fun _ => q 1, q 0))
  have e' := (gm_res (𝟙 X) y _ hm _).symm.trans (e₀.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div (pw L e) (L.pull m) (𝟙 X) y (fun _ => p 1, p 0) (fun _ => q 1, q 0) hm)
    (gm_res (𝟙 X) y _ hm _))))
  have g₁ := gm_pull_g L m (𝟙 X) y (fun _ => p 1) (fun _ => q 1) hm.1.1 hm.2.1
  have g₂ : gm (𝟙 X) y ((pw L e).U (p 0) ⊓ (pw L e).U (q 0)) ((pw L e).g (p 0) (q 0)) =
      gm (𝟙 X) y (L.U (p 0) ⊓ L.U (q 0)) (L.g (p 0) (q 0)) ^ e := map_zpow _ _ _
  have g₃ : gm (𝟙 X) y _ ((LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![e, -1]).g p q) =
      gm (𝟙 X) y (L.U (p 0) ⊓ L.U (q 0)) (L.g (p 0) (q 0)) ^ e *
        gm (𝟙 X ≫ m) y (L.U (p 1) ⊓ L.U (q 1)) (L.g (p 1) (q 1)) ^ (-1 : ℤ) := by
    refine (gm_linComb L ![𝟙 X, m] ![e, -1] (𝟙 X) y p q hy.1 hy.2).trans ?_
    rw [Fin.prod_univ_two]
    rfl
  have e'' := e'.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) g₁ (congrArg (·⁻¹) g₂)) rfl)
  refine ((gm_res (𝟙 X) y _ hy _).trans (val p hy.1)).trans ((congrArg (·⁻¹) e'').trans (Eq.symm ?_))
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) g₃ ((gm_res (𝟙 X) y _ hy _).trans (val q hy.2))).trans ?_)
  exact mul_eq_one_of_covolume_identity _ _ _

theorem isFinite_mulA : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → IsFinite (mulA B n).left := by
  intro K _ _ B _ hB n hn
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple K B hB
  obtain ⟨w, hw⟩ := GlobalTheory.MulPullAny.mulPull_of_symm K B hB H hH hsym n
  obtain ⟨α, hα⟩ := exists_gen H (mulA B n).left _ w hw
  have := hB.proper
  exact GlobalTheory.MulFinite.isFinite_of_relAmple B H hH (relAmple_of_veryAmpleBy' hH s hs) _ (n ^ 2)
    (by positivity) α hα

end GlobalTheory.MulFiniteAny
end
end
