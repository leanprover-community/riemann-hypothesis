import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformFirstCohomologyKernelsExist
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubPairRight
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimageStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningAffinePreimage
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpensStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechRestrictionCommutes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalLiftSectionsNonvanishing

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem basicOpen_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen (rs X h f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ X.basicOpen (s.f k) :=
  TopologicalSpace.Opens.mem_iSup

theorem basicOpen_eq_inf_nonzeroLocus {X : Scheme.{0}} {H : LB X} (a b : LB.Sec H)
    (r : Γ(X, nonzeroLocus a))
    (hr : ∀ k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (b.f k) =
      rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) r *
        rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) :
    X.basicOpen r = nonzeroLocus a ⊓ nonzeroLocus b := by
  have key : ∀ (k : H.ι) (x : X), x ∈ nonzeroLocus a → x ∈ H.U k →
      (x ∈ X.basicOpen (b.f k) ↔ x ∈ X.basicOpen r ∧ x ∈ X.basicOpen (a.f k)) := by
    intro k x hxa hxk
    have h := congrArg X.basicOpen (hr k)
    rw [Scheme.basicOpen_mul, basicOpen_rs, basicOpen_rs, basicOpen_rs] at h
    have hx : x ∈ nonzeroLocus a ⊓ H.U k := ⟨hxa, hxk⟩
    constructor
    · intro hb
      have : x ∈ (nonzeroLocus a ⊓ H.U k) ⊓ X.basicOpen (b.f k) := ⟨hx, hb⟩
      rw [h] at this
      exact ⟨this.1.2, this.2.2⟩
    · rintro ⟨h₁, h₂⟩
      have : x ∈ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen r) ⊓
          (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen (a.f k)) := ⟨⟨hx, h₁⟩, ⟨hx, h₂⟩⟩
      rw [← h] at this
      exact this.2
  apply le_antisymm
  · intro x hx
    have hxa : x ∈ nonzeroLocus a := X.basicOpen_le r hx
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff a x).1 hxa
    exact ⟨hxa, (mem_nonzeroLocus_iff b x).2
      ⟨k, (key k x hxa (X.basicOpen_le _ hk)).2 ⟨hx, hk⟩⟩⟩
  · rintro x ⟨hxa, hxb⟩
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff b x).1 hxb
    exact ((key k x hxa (X.basicOpen_le _ hk)).1 hk).1

theorem exists_basicOpen_eq_inf_iInf {X : Scheme.{0}} {H : LB X} {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) (i : Fin (m + 1))
    (hi : ∀ j, ∃ r : Γ(X, nonzeroLocus (s i)),
      X.basicOpen r = nonzeroLocus (s i) ⊓ nonzeroLocus (s j))
    (S : Finset (Fin (m + 1))) :
    ∃ f : Γ(X, nonzeroLocus (s i)),
      X.basicOpen f = nonzeroLocus (s i) ⊓ ⨅ j ∈ S, nonzeroLocus (s j) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert j S _ ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨r, hr⟩ := hi j
    refine ⟨f * r, ?_⟩
    rw [Scheme.basicOpen_mul, hf, hr, Finset.iInf_insert]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    tauto

theorem isAffineOpen_iInf_nonzeroLocus {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    (h : VeryAmpleBy f H s) {S : Finset (Fin (m + 1))} (hS : S.Nonempty) :
    IsAffineOpen (⨅ i ∈ S, nonzeroLocus (s i)) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨hA, r, hr, -⟩ := h.2 i
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_inf_iInf s i
    (fun j => ⟨r j, basicOpen_eq_inf_nonzeroLocus (s i) (s j) (r j) (hr j)⟩) S
  have e : ⨅ j ∈ S, nonzeroLocus (s j) = X.basicOpen g := by
    rw [hg]
    exact (inf_eq_right.2 (iInf₂_le i hi)).symm
  rw [e]
  exact hA.basicOpen g

theorem surjective_spec_of_nilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [_root_.range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isNilpotent_ker_factor {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  change _ = ⊥
  rw [eq_bot_iff, ← Ideal.map_quotient_self (I ^ (e + 1 + 1))]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

theorem exists_orderIso_opens {X X' : Scheme.{0}} (β : X ⟶ X') [IsClosedImmersion β]
    [Surjective β] : ∃ Φ : X.Opens ≃o X'.Opens, ∀ U, β ⁻¹ᵁ Φ U = U := by
  let h : X ≃ₜ X' := (β.isClosedEmbedding.isEmbedding).toHomeomorphOfSurjective β.surjective
  refine ⟨h.opensCongr, fun U => ?_⟩
  ext x
  have e : h.symm (β x) = x := h.symm_apply_apply x
  simp [h] at e ⊢
  rw [e]

theorem exists_orderIso_opens_tower (X : ℕ → Scheme.{0}) (β : ∀ e, X e ⟶ X (e + 1))
    [∀ e, IsClosedImmersion (β e)] [∀ e, Surjective (β e)] :
    ∃ G : ∀ e, (X 0).Opens ≃o (X e).Opens, (∀ U, G 0 U = U) ∧
      ∀ e U, β e ⁻¹ᵁ G (e + 1) U = G e U := by
  choose Φ hΦ using fun e => exists_orderIso_opens (β e)
  let G : ∀ e, (X 0).Opens ≃o (X e).Opens := fun e =>
    Nat.rec (OrderIso.refl _) (fun e G => G.trans (Φ e)) e
  exact ⟨G, fun _ => rfl, fun e U => hΦ e (G e U)⟩

theorem exists_basicOpens_of_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  intro R _ I Y β hβ H m s _ hV
  have hg := fun e => Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))
  have hci : ∀ e, IsClosedImmersion (β e) := fun e =>
    have : IsClosedImmersion (thickTrans R I e) := .spec_of_surjective _ (hg e)
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hβ e).flip this
  have hsu : ∀ e, Surjective (β e) := fun e =>
    have : Surjective (thickTrans R I e) :=
      surjective_spec_of_nilpotent_ker _ (hg e) (isNilpotent_ker_factor I e)
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip this
  obtain ⟨G, hG0, hG⟩ := exists_orderIso_opens_tower (fun e => (Y e).left) β
  have hinj : ∀ e (U V : (Y (e + 1)).left.Opens), β e ⁻¹ᵁ U = β e ⁻¹ᵁ V → U = V := by
    intro e U V h
    ext x
    obtain ⟨y, rfl⟩ := (β e).surjective x
    exact Set.ext_iff.1 (congrArg (fun W : (Y e).left.Opens => (W : Set _)) h) y
  refine ⟨fun e S => G e (⨅ i ∈ S, nonzeroLocus (s i)), fun S => hG0 _, fun e S => hG e _,
    fun e S S' h => (G e).monotone (biInf_mono h), fun e S j => ?_, fun e => ?_, ?_⟩
  · beta_reduce
    rw [← map_inf, Finset.iInf_insert, Finset.iInf_singleton, inf_comm]
  · beta_reduce
    simp only [Finset.iInf_singleton]
    rw [← OrderIso.map_iSup, hV.1, OrderIso.map_top]
  · intro e S hS
    beta_reduce
    induction e with
    | zero =>
      rw [hG0]
      exact isAffineOpen_iInf_nonzeroLocus hV hS
    | succ e ih =>
      obtain ⟨D, hD, he⟩ := GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
        _ _ _ (hg e) (isNilpotent_ker_factor I e) _ _ (Y (e + 1)).hom (Y e).hom (β e) (hβ e) _ ih
      rwa [hinj e _ _ (he.trans (hG e _).symm)] at hD

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_very_ample_opens_exist : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_basicOpens_of_tower
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem cst_thick_eq_zero {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (V : X.Opens) {r : R}
    (hr : r ∈ I ^ (e + 1)) : AbLaw.cst (p ≫ thick R I e) V r = 0 := by
  have key : AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V =
      (AbLaw.cst p V).comp (Ideal.Quotient.mk (I ^ (e + 1))) := by
    ext a
    have := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
    simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rw [this]
  have h0 : AbLaw.cst (p ≫ thick R I e) V r =
      AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1))))) V r := rfl
  rw [h0, key, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]

theorem pow_smul_top_secOnR (R : Type) [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left)
    (V : (Y e).left.Opens) :
    I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro r hr s _
  rw [Submodule.mem_bot, SecOnR.smul_def, cst_thick_eq_zero I e (Y e).hom V hr, zero_smul]

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_power_annihilates_sections : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (e : ℕ) (M : LB (Y e).left) (V : (Y e).left.Opens), I ^ (e + 1) • (⊤ : Submodule R (SecOnR (toR I Y e) M V)) = ⊥ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.pow_smul_top_secOnR
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem inv_of_mul_eq {A : Type} [CommRing A] {a a' b b' g g' : A} (h : a = g * b) (ha : a * a' = 1)
    (hb : b * b' = 1) (hg : g * g' = 1) : a' = g' * b' := by
  linear_combination (-(g' * b' * a')) * h + (g' * b') * ha + (-a') * hb + (-(a' * b * b')) * hg

variable {X X' : Scheme.{0}}

theorem exists_inv_of_isUnit_coord {N : LB X} {a : ℤ} {V : X.Opens} (x : SecOn (pw N a) V)
    (hx : ∀ k : N.ι, IsUnit (GlobalTheory.LB.coord x k)) :
    ∃ y : SecOn (pw N (-a)) V, secMulOn rfl x y = oneOn N (add_neg_cancel a) V := by
  have hy : (fun k : N.ι => (((hx k).unit⁻¹ : Γ(X, V ⊓ N.U k)ˣ) : Γ(X, V ⊓ N.U k))) ∈
      Geo.Tor.secOn (pw N (-a)) V := by
    intro i j
    have h := GlobalTheory.LB.coord_rel x i j (W := V ⊓ N.U i ⊓ N.U j) inf_le_left
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    refine inv_of_mul_eq h ?_ ?_ ?_
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx i))).trans (map_one _))
    · exact (map_mul _ _ _).symm.trans ((congrArg _ (IsUnit.mul_val_inv (hx j))).trans (map_one _))
    · refine (map_mul _ _ _).symm.trans ?_
      have e : ((N.g i j ^ a : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) *
          ((N.g i j ^ (-a) : Γ(X, N.U i ⊓ N.U j)ˣ) : Γ(X, N.U i ⊓ N.U j)) = 1 := by
        rw [← Units.val_mul, zpow_neg, mul_inv_cancel, Units.val_one]
      exact (congrArg _ e).trans (map_one _)
  refine ⟨GlobalTheory.LB.mkSec _ hy, GlobalTheory.LB.sec_ext fun k => ?_⟩
  exact IsUnit.mul_val_inv (hx k)

theorem isUnit_coord_of_congr (π : X' ⟶ X) (hπ : Function.Surjective π) {M : LB X} {L : LB X'}
    (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L (M.pull π)) (hw : w.IsGen) {V : X.Opens}
    {V' : X'.Opens} (e : π ⁻¹ᵁ V = V') (x : SecOn M V) (t : SecOn L V')
    (h : SecOn.congr hL (LB.isLB_pull hM π) w hw V' t = SecOn.pullLE M π V V' e.ge x)
    (ht : ∀ q, IsUnit (GlobalTheory.LB.coord t q)) (k : M.ι) : IsUnit (GlobalTheory.LB.coord x k) := by
  have hb : V ⊓ M.U k ≤ X.basicOpen (GlobalTheory.LB.coord x k) := by
    intro z hz
    obtain ⟨z', rfl⟩ := hπ z
    let j : (M.pull π).ι := fun _ => k
    have hz₁ : z' ∈ V' := e.le hz.1
    have hz₂ : z' ∈ (M.pull π).U j := by rw [pull_U]; exact hz.2
    obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.1
      (hL.cover.ge (TopologicalSpace.Opens.mem_top z'))
    let O : X'.Opens := V' ⊓ (M.pull π).U j ⊓ L.U q
    have hp : O ≤ V' ⊓ (M.pull π).U j := inf_le_left
    have hq' : O ≤ V' ⊓ L.U q := inf_le_inf_right _ inf_le_left
    have hpq : O ≤ (M.pull π).U j ⊓ L.U q := inf_le_inf_right _ inf_le_right
    have c := SecOn.coord_congr hL (LB.isLB_pull hM π) w hw t j q hp hq' hpq
    rw [h] at c
    have hu : IsUnit (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [c]
      exact (Units.isUnit _).map (rs X' hpq) |>.mul ((ht q).map (rs X' hq'))
    have hz' : z' ∈ X'.basicOpen (rs X' hp (GlobalTheory.LB.coord (SecOn.pullLE M π V V' e.ge x) j)) := by
      rw [X'.basicOpen_of_isUnit hu]
      exact ⟨⟨hz₁, hz₂⟩, hq⟩
    erw [Scheme.basicOpen_res] at hz'
    have hz'' := hz'.2
    rw [SecOn.coord_pullLE, Scheme.basicOpen_appLE] at hz''
    exact hz''.2
  have hu : IsUnit (rs X (X.basicOpen_le _) (GlobalTheory.LB.coord x k)) :=
    X.toRingedSpace.isUnit_res_basicOpen (GlobalTheory.LB.coord x k)
  simpa only [rs_rs, rs_self] using hu.map (rs X hb)

variable {R : Type} [CommRing R] (I : Ideal R)

theorem ker_factor_le_nilradical (e : ℕ) (h : I ^ (e + 1 + 1) ≤ I ^ (e + 1)) :
    RingHom.ker (Ideal.Quotient.factor h) ≤ nilradical (R ⧸ I ^ (e + 1 + 1)) := by
  intro x hx
  rw [RingHom.mem_ker] at hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
  rw [mem_nilradical]
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  have hy2 : y ^ 2 ∈ I ^ (e + 1) * I ^ (e + 1) := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hx
  rw [← pow_add] at hy2
  exact Ideal.pow_le_pow_right (by omega) hy2

theorem surjective_thickTrans (e : ℕ) : Surjective (thickTrans R I e) := by
  delta ReciprocityTheory.ChartRestriction.G.Out.thickTrans
  have key : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), Function.Surjective φ →
      RingHom.ker φ ≤ nilradical A → Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    intro A B _ _ φ hφ hker
    constructor
    intro p
    haveI := p.isPrime
    have hk : RingHom.ker φ ≤ p.asIdeal := le_trans hker (nilradical_le_prime p.asIdeal)
    refine ⟨⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩, ?_⟩
    show PrimeSpectrum.comap φ ⟨p.asIdeal.map φ, Ideal.map_isPrime_of_surjective hφ hk⟩ = p
    ext1
    show Ideal.comap φ (Ideal.map φ p.asIdeal) = p.asIdeal
    rw [Ideal.comap_map_of_surjective' φ hφ, sup_eq_left.mpr hk]
  exact key _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_le_nilradical I e _)

variable (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))

include hβ in

theorem surjective_tower (e : ℕ) : Function.Surjective (β e) := by
  exact (MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans I e)).surj

theorem isUnit_coord_of_redL (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) {V : (Y (e + 1)).left.Opens}
    {V' : (Y e).left.Opens} (h : β e ⁻¹ᵁ V = V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (ht : ∀ q, IsUnit (SecOnR.coord (redL I Y β hβ L w hL e V V' h.ge x) q)) (k : (L (e + 1)).ι) :
    IsUnit (SecOnR.coord x k) :=
  isUnit_coord_of_congr (β e) (surjective_tower I Y β hβ e) (hL e).1 (hL (e + 1)).1 (w e) (hL e).2 h
    x (redL I Y β hβ L w hL e V V' h.ge x)
    ((SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
      (hL e).2 V')).apply_symm_apply _) ht k

theorem exists_lifts_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hge : ∀ e (S : Finset (Fin (m + 1))), D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have hsurj : ∀ e (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red I Y N D β hβ v hN hge (d : ℤ) e S) := fun e S hS =>
    (redL_surjective_ker R I Y β hβ (fun e => pw (N e) (d : ℤ)) (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)).1
  have hl : ∀ e (S : Finset (Fin (m + 1))) (t : SecOn (pw (N e) (d : ℤ)) (D e S)),
      ∃ x : SecOn (pw (N (e + 1)) (d : ℤ)) (D (e + 1) S), S.Nonempty →
        red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ x) = SecOnR.of _ _ _ t := by
    intro e S t
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hsurj e S hS (SecOnR.of _ _ _ t)
      exact ⟨(SecOnR.of _ _ _).symm x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hS⟩
  choose lf hlf using hl
  let sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S) :=
    fun e j S => Nat.rec (motive := fun e => SecOn (pw (N e) (d : ℤ)) (D e S))
      (GlobalTheory.LB.ofSec (s j) (D 0 S)) (fun e t => lf e S t) e
  refine ⟨sh, fun j S _ => rfl, fun e j S hS => hlf e S _ hS, fun e i S hi =>
    exists_inv_of_isUnit_coord _ ?_⟩
  induction e with
  | zero =>
    intro k
    have hle : D 0 S ≤ nonzeroLocus (s i) := by
      rw [hD0]
      exact iInf₂_le i hi
    exact SecOn.isUnit_rs_of_le_nonzeroLocus (s i) k (inf_le_right : D 0 S ⊓ (N 0).U k ≤ (N 0).U k)
      (inf_le_left.trans hle)
  | succ e ih =>
    intro k
    refine isUnit_coord_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
      (fun e => pullPow (v e) (d : ℤ))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (hDβ e S)
      (SecOnR.of _ _ _ (sh (e + 1) i S)) (fun q => ?_) k
    have hr : red I Y N D β hβ v hN hge (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) i S)) =
        SecOnR.of _ _ _ (sh e i S) := hlf e S (sh e i S) ⟨i, hi⟩
    change IsUnit (SecOnR.coord (red I Y N D β hβ v hN hge (d : ℤ) e S
      (SecOnR.of _ _ _ (sh (e + 1) i S))) q)
    rw [hr]
    exact ih q

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_very_ample_sections : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)), ∃ sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S), (∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) ∧ (∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) ∧ (∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_lifts_tower
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_cech_cover_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.red_secMulOn <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mem_smul_top_of_redL {R : Type} [CommRing R] (I : Ideal R)
    (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
    (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
    (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
    (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V : (Y (e + 1)).left.Opens)
    (V' : (Y e).left.Opens) (h : β e ⁻¹ᵁ V = V') (hV : IsAffineOpen V)
    (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V)
    (hx : redL I Y β hβ L w hL e V V' h.ge x ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V'))) :
    x ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) := by
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.thickening_affine_preimage R I Y β hβ L w hL e V V' h hV
  have hmap : Submodule.map (redL I Y β hβ L w hL e V V' h.ge)
      (I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V))) =
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (L e) V')) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hsurj]
  rw [← hmap] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  have hk : x - z ∈ LinearMap.ker (redL I Y β hβ L w hL e V V' h.ge) := by
    rw [LinearMap.mem_ker, map_sub, hzx, sub_self]
  rw [hker] at hk
  have hk' : x - z ∈ I • (⊤ : Submodule R (SecOnR (toR I Y (e + 1)) (L (e + 1)) V)) :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero e)) hk
  simpa using Submodule.add_mem _ hk' hz

theorem map_mul_sub_mul {A B : Type} [CommRing A] [CommRing B] (ρ : A →+* B) (x y : A) (z : B) :
    ρ (x * y) - ρ x * z = (ρ y - z) * ρ x := by
  rw [map_mul]; ring

theorem map_mem_smul_top {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (I : Ideal R) (φ : M →ₗ[R] M') {x : M}
    (hx : x ∈ I • (⊤ : Submodule R M)) : φ x ∈ I • (⊤ : Submodule R M') := by
  have h := Submodule.mem_map_of_mem (f := φ) hx
  rw [Submodule.map_smul''] at h
  exact Submodule.smul_mono le_rfl le_top h

theorem resT_mulT_sub_mem : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu j e t S S' h a hS
  have hS' : S'.Nonempty := hS.mono h

  have key : ∀ e : ℕ, SecOnR.restrict (toR I Y e) (pw (N e) (d : ℤ)) (hDm e S S' h)
        (SecOnR.of _ _ _ (sh e j S)) - SecOnR.of (toR I Y e) _ _ (sh e j S') ∈
      I • (⊤ : Submodule R (SecOnR (toR I Y e) (pw (N e) (d : ℤ)) (D e S'))) := by
    intro e
    induction e with
    | zero =>
      have : SecOnR.restrict (toR I Y 0) (pw (N 0) (d : ℤ)) (hDm 0 S S' h)
          (SecOnR.of _ _ _ (sh 0 j S)) - SecOnR.of (toR I Y 0) _ _ (sh 0 j S') = 0 := by
        rw [hsh0 j S hS, hsh0 j S' hS', sub_eq_zero]
        exact GlobalTheory.LB.map_ofSec (s j) (hDm 0 S S' h)
      rw [this]
      exact Submodule.zero_mem _
    | succ e ih =>
      refine mem_smul_top_of_redL I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S')
        (D e S') (hDβ e S') (hDa (e + 1) S' hS') _ ?_
      rw [map_sub]
      have h1 := GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) (d : ℤ))
        (fun e => pullPow (v e) (d : ℤ))
        (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
        (D (e + 1) S') (D e S) (D e S') (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h)
        (hDm e S S' h) (SecOnR.of _ _ _ (sh (e + 1) j S))
      have h2 := hshp e j S hS
      have h3 := hshp e j S' hS'
      rw [h1]
      erw [h2, h3]
      exact ih
  have hmem := map_mem_smul_top I
    (mulRight (toR I Y e) (show (d : ℤ) + (d : ℤ) * t = (d : ℤ) * (t + 1) by ring)
      ((SecOnR.of _ _ _).symm (resT I Y N D (d : ℤ) hDm e t h a))) (key e)
  convert hmem using 1
  refine SecOnR.ext fun (i : (N e).ι) => ?_
  exact map_mul_sub_mul (rs (Y e).left (inf_le_inf_right ((N e).U i) (hDm e S S' h)))
    (SecOnR.coord a i) (GlobalTheory.LB.coord (sh e j S) i) (GlobalTheory.LB.coord (sh e j S') i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_sections_generate : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (j : Fin (m + 1)) (e : ℕ) (t : ℤ) (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm I Y N D (d : ℤ) e t S), S.Nonempty → resT I Y N D (d : ℤ) hDm e (t + 1) h (mulT I Y N D (d : ℤ) e t S (sh e j S) a) - mulT I Y N D (d : ℤ) e t S' (sh e j S') (resT I Y N D (d : ℤ) hDm e t h a) ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (t + 1) S')) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.resT_mulT_sub_mem
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_twisted_section_transition : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.mulT_bijective_of_inverse <;> assumption)
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem exists_form_of_eval {ι R B G : Type} [CommRing R] [CommRing B] [AddCommGroup G]
    [Module (MvPolynomial ι R) G] (φ : R →+* B) (r : ι → B) (μ : B →+ G) (i : ι)
    (hC : ∀ (a : R) (c : B), μ (φ a * c) = (MvPolynomial.C a : MvPolynomial ι R) • μ c)
    (hr : ∀ (j : ι) (c : B), (MvPolynomial.X i : MvPolynomial ι R) • μ (r j * c) =
      (MvPolynomial.X j : MvPolynomial ι R) • μ c) (P : MvPolynomial ι R) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ Q : MvPolynomial ι R, Q.IsHomogeneous n ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ n • μ (MvPolynomial.eval₂Hom φ r P) = Q • μ 1 := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨0, fun n _ => ⟨MvPolynomial.X i ^ n * MvPolynomial.C a, ?_, ?_⟩⟩
    · simpa using (MvPolynomial.isHomogeneous_X_pow (R := R) i n).mul
        (MvPolynomial.isHomogeneous_C (σ := ι) a)
    · have h := hC a 1
      rw [mul_one] at h
      rw [MvPolynomial.eval₂Hom_C, h, mul_smul]
  | add p q hp hq =>
    obtain ⟨n₁, h₁⟩ := hp
    obtain ⟨n₂, h₂⟩ := hq
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    obtain ⟨Q₁, a₁, b₁⟩ := h₁ n (le_trans (le_max_left _ _) hn)
    obtain ⟨Q₂, a₂, b₂⟩ := h₂ n (le_trans (le_max_right _ _) hn)
    refine ⟨Q₁ + Q₂, a₁.add a₂, ?_⟩
    rw [map_add, map_add, smul_add, b₁, b₂, add_smul]
  | mul_X p j hp =>
    obtain ⟨n₀, h⟩ := hp
    refine ⟨n₀ + 1, fun n hn => ?_⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨Q, a, b⟩ := h n' (by omega)
    refine ⟨MvPolynomial.X j * Q, ?_, ?_⟩
    · simpa [add_comm] using (MvPolynomial.isHomogeneous_X R j).mul a
    · rw [map_mul, MvPolynomial.eval₂Hom_X', mul_comm (MvPolynomial.eval₂Hom φ r p), pow_succ, mul_smul,
        hr, smul_smul, mul_comm _ (MvPolynomial.X j), mul_smul, b, smul_smul]

section Shift

variable {ι R : Type} [CommRing R] {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
  {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)

theorem exists_pow_smul_of_eq_zero (i : ι) (k : ℕ) : ∀ (t : ℤ) (a : A t), t + k = 0 →
    ∃ b : A 0, (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a = GrSum.of hx 0 b := by
  induction k with
  | zero =>
    intro t a h
    obtain rfl : t = 0 := by simpa using h
    exact ⟨a, by simp⟩
  | succ k ih =>
    intro t a h
    obtain ⟨b, hb⟩ := ih (t + 1) (x i t a) (by push_cast at h; omega)
    exact ⟨b, by rw [pow_succ, mul_smul, GrSum.X_smul_of, hb]⟩

theorem exists_of_eq_pow_smul (i : ι) (hb : ∀ t, Function.Surjective (x i t)) (k : ℕ) :
    ∀ (t : ℤ) (a : A t), t = k →
    ∃ b : A 0, GrSum.of hx t a = (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx 0 b := by
  induction k with
  | zero =>
    intro t a h
    obtain rfl : t = 0 := by simpa using h
    exact ⟨a, by simp⟩
  | succ k ih =>
    intro t a h
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by ring⟩
    obtain ⟨a', rfl⟩ := hb t' a
    obtain ⟨b, hb'⟩ := ih t' a' (by push_cast at h; omega)
    exact ⟨b, by rw [← GrSum.X_smul_of, hb', pow_succ', mul_smul]⟩

theorem exists_shift_zero (i : ι) (hb : ∀ t, Function.Surjective (x i t)) (t : ℤ) (a : A t) :
    ∃ (k l : ℕ) (b : A 0), (k : ℤ) + t = l ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a =
        (MvPolynomial.X i : MvPolynomial ι R) ^ l • GrSum.of hx 0 b := by
  rcases le_total t 0 with h | h
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, t + k = 0 := ⟨(-t).toNat, by omega⟩
    obtain ⟨b, hb'⟩ := exists_pow_smul_of_eq_zero hx i k t a hk
    exact ⟨k, 0, b, by push_cast; omega, by simpa using hb'⟩
  · obtain ⟨l, hl⟩ : ∃ l : ℕ, t = l := ⟨t.toNat, by omega⟩
    obtain ⟨b, hb'⟩ := exists_of_eq_pow_smul hx i hb l t a hl
    exact ⟨0, l, b, by simp [hl], by simpa using hb'⟩

end Shift

theorem exists_smul_oneOn {X : Scheme.{0}} {N : LB X} (hN : N.IsLB) {a : ℤ} (h : a = 0) (V : X.Opens)
    (x : SecOn (pw N a) V) : ∃ c : Γ(X, V), c • oneOn N h V = x := by
  subst h
  obtain ⟨c, hc⟩ := GlobalTheory.LB.exists_fun_of_cover (fun k => V ⊓ N.U k) (fun k => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf hN.cover V) (fun k => GlobalTheory.LB.coord x k) (fun k l => by
      have := GlobalTheory.LB.coord_rel x k l (W := (V ⊓ N.U k) ⊓ (V ⊓ N.U l)) inf_le_left inf_le_right
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      rw [show (AbLaw.pw N 0).g k l = N.g k l ^ (0 : ℤ) from rfl, zpow_zero, Units.val_one] at this
      erw [map_one, one_mul] at this
      exact this)
  refine ⟨c, GlobalTheory.LB.sec_ext fun k => ?_⟩
  rw [GlobalTheory.LB.coord_smul]
  erw [hc k]
  exact mul_one _

section Chart

variable {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R)) {N : LB X}
  (d : ℤ) {V : X.Opens} {ι : Type}

theorem exists_form_chart (hN : N.IsLB) (σ : ι → SecOn (pw N d) V)
    (hx : OperatorsCommute (ι := ι) (R := R) (A := fun t => SecOnR f (pw N (d * t)) V)
      fun j t => mulRight f (by ring) (σ j)) (i : ι)
    (hb : ∀ t : ℤ, Function.Surjective
      (mulRight (a := d * t) (c := d * (t + 1)) f (by ring) (σ i)))
    (r : ι → Γ(X, V))
    (hr : ∀ j (k : (pw N d).ι), GlobalTheory.LB.coord (σ j) k =
      rs X (inf_le_left : V ⊓ (pw N d).U k ≤ V) (r j) * GlobalTheory.LB.coord (σ i) k)
    (hs : Function.Surjective (MvPolynomial.eval₂Hom (cst f V) r)) (t : ℤ)
    (a : SecOnR f (pw N (d * t)) V) :
    ∃ (k n : ℕ) (Q : MvPolynomial ι R), Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of hx t a =
        Q • GrSum.of hx 0 (SecOnR.of f _ V (oneOn N (mul_zero d) V)) := by
  set one : SecOnR f (pw N (d * 0)) V := SecOnR.of f _ V (oneOn N (mul_zero d) V) with hone
  let μ : Γ(X, V) →+ GrSum hx := AddMonoidHom.mk' (fun c => GrSum.of hx 0 (c • one))
    (fun a b => by rw [add_smul, map_add])
  have hμ : ∀ c, μ c = GrSum.of hx 0 (c • one) := fun _ => rfl
  have hC : ∀ (a : R) (c : Γ(X, V)), μ (cst f V a * c) =
      (MvPolynomial.C a : MvPolynomial ι R) • μ c := by
    intro a c
    rw [← MvPolynomial.algebraMap_eq, algebraMap_smul, hμ, hμ, mul_smul, ← SecOnR.smul_def, map_smul]
  have hr' : ∀ (j : ι) (c : Γ(X, V)), (MvPolynomial.X i : MvPolynomial ι R) • μ (r j * c) =
      (MvPolynomial.X j : MvPolynomial ι R) • μ c := by
    intro j c
    rw [hμ, hμ, GrSum.X_smul_of, GrSum.X_smul_of]
    congr 1
    refine SecOnR.ext fun (k : N.ι) => ?_
    let cd : ι → Γ(X, V ⊓ N.U k) := fun l => GlobalTheory.LB.coord (σ l) k
    change (rs X (inf_le_left : V ⊓ N.U k ≤ V) (r j * c) * (1 : Γ(X, V ⊓ N.U k))) * cd i =
      (rs X (inf_le_left : V ⊓ N.U k ≤ V) c * (1 : Γ(X, V ⊓ N.U k))) * cd j
    have hk : cd j = rs X (inf_le_left : V ⊓ N.U k ≤ V) (r j) * cd i := hr j k
    rw [hk, map_mul]
    ring
  obtain ⟨k, l, b, hkl, hab⟩ := exists_shift_zero hx i hb t a
  obtain ⟨c, hc⟩ := exists_smul_oneOn hN (mul_zero d) V ((SecOnR.of f _ V).symm b)
  obtain ⟨P, rfl⟩ := hs c
  obtain ⟨n₀, h⟩ := exists_form_of_eval (cst f V) r μ i hC hr' P
  obtain ⟨Q, hQ, hQe⟩ := h n₀ le_rfl
  have hb' : GrSum.of hx 0 b = μ (MvPolynomial.eval₂Hom (cst f V) r P) := by
    rw [hμ]; congr 1; exact hc.symm
  have h1 : μ 1 = GrSum.of hx 0 one := by rw [hμ, one_smul]
  refine ⟨n₀ + k, l + n₀, MvPolynomial.X i ^ l * Q, ?_, ?_, ?_⟩
  · exact (MvPolynomial.isHomogeneous_X_pow (R := R) i l).mul hQ
  · push_cast; omega
  · rw [pow_add, mul_smul, hab, hb', smul_comm, hQe, h1, mul_smul]

end Chart

section Step

variable (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e)))
  (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) {ι : Type}
  (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S)
  (S : Finset ι) (hDa : ∀ e, IsAffineOpen (D e S))
  (sh : ∀ e (_ : ι), SecOn (pw (N e) d) (D e S))
  (hshp : ∀ e j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) d e S (SecOnR.of _ _ _ (sh (e + 1) j)) =
    SecOnR.of _ _ _ (sh e j))
  (hc : ∀ e, OperatorsCommute (ι := ι) (R := R) (A := fun t => Tm I Y N D d e t S)
    fun j t => mulT I Y N D d e t S (sh e j))

include hshp hDa in

theorem form_step (i : ι) (e : ℕ)
    (ih : ∀ (t : ℤ) (a : Tm I Y N D d e t S), ∃ (k n : ℕ) (Q : MvPolynomial ι R)
      (w : Tm I Y N D d e (n : ℤ) S), Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D d e (n : ℤ) S)) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc e) t a =
        Q • GrSum.of (hc e) 0 (oneT I Y N D d e S) + GrSum.of (hc e) (n : ℤ) w)
    (t : ℤ) (a : Tm I Y N D d (e + 1) t S) :
    ∃ (k n : ℕ) (Q : MvPolynomial ι R) (w : Tm I Y N D d (e + 1) (n : ℤ) S),
      Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)) ∧
      (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1)) t a =
        Q • GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S) +
          GrSum.of (hc (e + 1)) (n : ℤ) w := by
  let ρ : ∀ n : ℤ, Tm I Y N D d (e + 1) n S →ₗ[R] Tm I Y N D d e n S := fun n =>
    red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d * n) e S
  have hred : ∀ n : ℤ, Function.Surjective (ρ n) ∧
      LinearMap.ker (ρ n) = I ^ (e + 1) • ⊤ := fun n =>
    GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) (d * n)) (fun e => pullPow (v e) (d * n))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1))
  have hφ : ∀ (j : ι) (n : ℤ) (x : Tm I Y N D d (e + 1) n S),
      ρ (n + 1) (mulT I Y N D d (e + 1) n S (sh (e + 1) j) x) =
        mulT I Y N D d e n S (sh e j) (ρ n x) := by
    intro j n x
    have := red_secMulOn R I Y β hβ N v hN ι D (fun e S => (hDβ e S).ge) (d * n) d (d * (n + 1))
      (by ring) e S ((SecOnR.of _ _ _).symm x) (sh (e + 1) j)
    rw [hshp e j] at this
    exact this
  have hone : ρ 0 (oneT I Y N D d (e + 1) S) = oneT I Y N D d e S :=
    GlobalTheory.T.thickening_cech_restriction_commutes R I Y β hβ N v hN ι D (fun e S => (hDβ e S).ge) (d * 0) (mul_zero d) e S
  obtain ⟨k, n, Q, w, hQ, hk, hw, he⟩ := ih t (ρ t a)
  obtain ⟨w', hw', rfl⟩ : ∃ w' ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)),
      ρ n w' = w := by
    have : (I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S))).map (ρ n) = I • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 (hred n).1]
    rw [← this] at hw
    exact hw
  let G := GrSum.map (hc (e + 1)) (hc e) ρ hφ
  have h1 : (MvPolynomial.X i : MvPolynomial ι R) ^ k • GrSum.of (hc (e + 1)) t a ∈
      GrSum.grading (hc (e + 1)) (n : ℤ) := by
    have := grSMul_mem (GrSum.grading (hc (e + 1)))
      (mem_polyGrading_natCast.2 (MvPolynomial.isHomogeneous_X_pow (R := R) i k))
      (GrSum.of_mem_grading (hc (e + 1)) t a)
    rwa [show t + (k : ℤ) = n by omega] at this
  have h2 : Q • GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S) ∈
      GrSum.grading (hc (e + 1)) (n : ℤ) := by
    have := grSMul_mem (GrSum.grading (hc (e + 1))) (mem_polyGrading_natCast.2 hQ)
      (GrSum.of_mem_grading (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S))
    rwa [zero_add] at this
  obtain ⟨z, hz⟩ := sub_mem (sub_mem h1 h2) (GrSum.of_mem_grading (hc (e + 1)) (n : ℤ) w')
  have hGz : GrSum.of (hc e) (n : ℤ) (ρ n z) = 0 := by
    have := congrArg G hz
    rw [show G (GrSum.of (hc (e + 1)) (n : ℤ) z) = GrSum.of (hc e) (n : ℤ) (ρ n z) from
      GrSum.map_of _ _ _ _ _ _] at this
    rw [this, map_sub, map_sub, map_smul, map_smul]
    rw [show G (GrSum.of (hc (e + 1)) t a) = GrSum.of (hc e) t (ρ t a) from
        GrSum.map_of _ _ _ _ _ _,
      show G (GrSum.of (hc (e + 1)) 0 (oneT I Y N D d (e + 1) S)) =
        GrSum.of (hc e) 0 (ρ 0 (oneT I Y N D d (e + 1) S)) from GrSum.map_of _ _ _ _ _ _,
      show G (GrSum.of (hc (e + 1)) (n : ℤ) w') = GrSum.of (hc e) (n : ℤ) (ρ n w') from
        GrSum.map_of _ _ _ _ _ _, hone, he]
    abel
  have hz0 : ρ n z = 0 :=
    GrSum.of_injective (hc e) (n : ℤ) (hGz.trans (map_zero _).symm)
  have hzI : z ∈ I • (⊤ : Submodule R (Tm I Y N D d (e + 1) (n : ℤ) S)) := by
    have h3 : z ∈ LinearMap.ker (ρ n) := hz0
    rw [(hred n).2] at h3
    exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) h3
  refine ⟨k, n, Q, w' + z, hQ, hk, add_mem hw' hzI, ?_⟩
  rw [map_add, hz]
  abel

end Step

theorem cst_comp_specMap {X : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']
    (p : X ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (U : X.Opens) :
    AbLaw.cst (p ≫ Spec.map (CommRingCat.ofHom g)) U = (AbLaw.cst p U).comp g := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [AbLaw.cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem exists_form_add_ideal_smul : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)) (e : ℕ) (i : Fin (m + 1)) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k : ℕ) (q : MvPolynomial (Fin (m + 1)) R) (t' : ℤ) (w : Tm I Y N D (d : ℤ) e t' {i}), w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) + GrSum.of (hc e {i}) t' w := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc e i t a
  have hi : ({i} : Finset (Fin (m + 1))).Nonempty := Finset.singleton_nonempty i
  have key : ∀ (e : ℕ) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k n : ℕ)
      (Q : MvPolynomial (Fin (m + 1)) R) (w : Tm I Y N D (d : ℤ) e (n : ℤ) {i}),
      Q.IsHomogeneous n ∧ (k : ℤ) + t = n ∧
      w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e (n : ℤ) {i})) ∧
      (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a =
        Q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) +
          GrSum.of (hc e {i}) (n : ℤ) w := by
    intro e
    induction e with
    | zero =>
      intro t a
      obtain ⟨haff, r, hr, hsurj⟩ := hs.2 i
      have hV : D 0 {i} = nonzeroLocus (s i) := by rw [hD0]; simp
      have hbij : ∀ t : ℤ, Function.Surjective (mulRight (a := (d : ℤ) * t)
          (c := (d : ℤ) * (t + 1)) (toR I Y 0) (by ring) (sh 0 i {i})) := fun t => by
        obtain ⟨y, hy⟩ := hshu 0 i {i} (Finset.mem_singleton_self i)
        exact (mulT_bijective_of_inverse R I Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D 0 t {i} (sh 0 i {i}) y hy).2
      let r' : Fin (m + 1) → Γ((Y 0).left, D 0 {i}) := fun j => rs _ hV.le (r j)
      have hr' : ∀ j (k : (pw (N 0) (d : ℤ)).ι), GlobalTheory.LB.coord (sh 0 j {i}) k =
          rs _ (inf_le_left : D 0 {i} ⊓ (pw (N 0) (d : ℤ)).U k ≤ D 0 {i}) (r' j) *
            GlobalTheory.LB.coord (sh 0 i {i}) k := by
        intro j k
        have := congrArg (rs _ (inf_le_inf_right _ hV.le :
          D 0 {i} ⊓ (pw (N 0) (d : ℤ)).U k ≤ nonzeroLocus (s i) ⊓ (pw (N 0) (d : ℤ)).U k)) (hr j k)
        rw [map_mul, rs_rs, rs_rs, rs_rs] at this
        rw [hsh0 j _ hi, hsh0 i _ hi, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec]
        simp only [r', rs_rs]
        exact this
      have hcomp : MvPolynomial.eval₂Hom (cst (toR I Y 0) (D 0 {i})) r' =
          ((rs _ hV.le).comp (MvPolynomial.eval₂Hom (cst (Y 0).hom (nonzeroLocus (s i))) r)).comp
            (MvPolynomial.map (Ideal.Quotient.mk (I ^ (0 + 1)))) := by
        apply MvPolynomial.ringHom_ext
        · intro x
          have h1 := RingHom.congr_fun (cst_comp_specMap (Y 0).hom
            (Ideal.Quotient.mk (I ^ (0 + 1))) (D 0 {i})) x
          simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C, rs_cst]
          exact h1
        · intro j
          simp [r']
      have hs' : Function.Surjective (MvPolynomial.eval₂Hom (cst (toR I Y 0) (D 0 {i})) r') := by
        intro c
        obtain ⟨P₀, hP₀⟩ := hsurj (rs _ hV.ge c)
        obtain ⟨P, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective P₀
        refine ⟨P, ?_⟩
        rw [hcomp, RingHom.comp_apply, RingHom.comp_apply, hP₀, rs_rs, rs_self]
      obtain ⟨k, n, Q, hQ, hk, he⟩ := exists_form_chart (toR I Y 0) (d : ℤ) (hN 0).1
        (fun j => sh 0 j {i}) (hc 0 {i}) i hbij r' hr' hs' t a
      refine ⟨k, n, Q, 0, hQ, hk, zero_mem _, ?_⟩
      rw [map_zero, add_zero]
      exact he
    | succ e ih =>
      exact form_step R I Y β hβ N v hN (d : ℤ) D hDβ {i} (fun e => hDa e {i} hi)
        (fun e j => sh e j {i}) (fun e j => hshp e j {i} hi) (fun e => hc e {i}) i e ih
  obtain ⟨k, n, Q, w, -, -, hw, he⟩ := key e t a
  exact ⟨k, Q, n, w, hw, he⟩

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_closed_embedding : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (sh : ∀ e (j : Fin (m + 1)) (S : Finset (Fin (m + 1))), SecOn (pw (N e) (d : ℤ)) (D e S)) (hsh0 : ∀ j S, S.Nonempty → sh 0 j S = GlobalTheory.LB.ofSec (s j) (D 0 S)) (hshp : ∀ e j S, S.Nonempty → red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) (d : ℤ) e S (SecOnR.of _ _ _ (sh (e + 1) j S)) = SecOnR.of _ _ _ (sh e j S)) (hshu : ∀ e i S, i ∈ S → ∃ y : SecOn (pw (N e) (-(d : ℤ))) (D e S), secMulOn rfl (sh e i S) y = oneOn (N e) (add_neg_cancel (d : ℤ)) (D e S)) (hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R) (A := fun t => Tm I Y N D (d : ℤ) e t S) fun j t => mulT I Y N D (d : ℤ) e t S (sh e j S)) (e : ℕ) (i : Fin (m + 1)) (t : ℤ) (a : Tm I Y N D (d : ℤ) e t {i}), ∃ (k : ℕ) (q : MvPolynomial (Fin (m + 1)) R) (t' : ℤ) (w : Tm I Y N D (d : ℤ) e t' {i}), w ∈ I • (⊤ : Submodule R (Tm I Y N D (d : ℤ) e t' {i})) ∧ (MvPolynomial.X i : MvPolynomial (Fin (m + 1)) R) ^ k • GrSum.of (hc e {i}) t a = q • GrSum.of (hc e {i}) 0 (oneT I Y N D (d : ℤ) e {i}) + GrSum.of (hc e {i}) t' w := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_form_add_ideal_smul
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

variable {X X' : Scheme.{0}}

theorem pullLE_ofSec {M : LB X} (π : X' ⟶ X) (V : X.Opens) (V' : X'.Opens) (e : V' ≤ π ⁻¹ᵁ V)
    (s : LB.Sec M) :
    SecOn.pullLE M π V V' e (GlobalTheory.LB.ofSec s V) = GlobalTheory.LB.ofSec (secPull s π) V' := by
  refine GlobalTheory.LB.sec_ext fun j => ?_
  rw [SecOn.coord_pullLE, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.appLE_resG]
  change _ = resG X' _ ((π.appLE _ _ (GlobalTheory.LB.pull_U_le π j)).hom (s.f (j PUnit.unit)))
  rw [GlobalTheory.LB.resG_appLE]

theorem secMaps_of_cover {A B : LB X} (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen)
    {κ : Type} (O : κ → X.Opens) (hO : ⨆ a, O a = ⊤) (s : LB.Sec A) (t : LB.Sec B)
    (h : ∀ a, SecOn.congr hA hB w hw (O a) (GlobalTheory.LB.ofSec s (O a)) = GlobalTheory.LB.ofSec t (O a)) :
    SecMaps w s t := by
  rintro ⟨p, q⟩
  refine ext_germ fun x hx => ?_
  obtain ⟨a, ha⟩ : ∃ a, x ∈ O a := by
    have hx' : x ∈ (⨆ a, O a) := by rw [hO]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx'
  have hp : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ B.U p := inf_le_inf_left _ inf_le_left
  have hq : O a ⊓ (B.U p ⊓ A.U q) ≤ O a ⊓ A.U q := inf_le_inf_left _ inf_le_right
  have hh : O a ⊓ (B.U p ⊓ A.U q) ≤ B.U p ⊓ A.U q := inf_le_right
  have e := SecOn.coord_congr hA hB w hw (GlobalTheory.LB.ofSec s (O a)) p q hp hq hh
  rw [h a, GlobalTheory.LB.coord_ofSec, GlobalTheory.LB.coord_ofSec] at e
  have hxW : x ∈ O a ⊓ (B.U p ⊓ A.U q) := ⟨ha, hx⟩
  change resG X hp (resG X _ (t.f p)) = resG X hh _ * resG X hq (resG X _ (s.f q)) at e
  rw [resG_resG, resG_resG] at e
  refine (germ_resG hh x hxW _).symm.trans ((congrArg _ ?_).trans (germ_resG hh x hxW _))
  rw [map_mul, resG_resG, resG_resG]
  exact e

section Tower

variable {R : Type} [CommRing R] (I : Ideal R)
  (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
  (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left)
  (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e))
  (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e)))
  (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen)

include hL in

theorem congr_ofSec_of_redL (e : ℕ) (V : (Y (e + 1)).left.Opens) (V' : (Y e).left.Opens)
    (h : V' ≤ β e ⁻¹ᵁ V) (τ : LB.Sec (L (e + 1))) (σ : LB.Sec (L e))
    (hr : redL I Y β hβ L w hL e V V' h (SecOnR.of _ _ _ (GlobalTheory.LB.ofSec τ V)) =
      SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ V')) :
    SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 V'
      (GlobalTheory.LB.ofSec σ V') = GlobalTheory.LB.ofSec (secPull τ (β e)) V' := by
  have h1 := (LinearEquiv.symm_apply_eq _).1 hr
  rw [SecOnR.pull_of, SecOnR.linEquiv_of] at h1
  exact h1.symm.trans (pullLE_ofSec (β e) V V' h τ)

end Tower

theorem lift_of_cech_pairs : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  intro R _ I Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa t e hc σ
  have hLp : ∀ e, (pw (N e) ((d : ℤ) * t)).IsLB ∧ (pullPow (v e) ((d : ℤ) * t)).IsGen :=
    fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩

  have hres : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (x : Tm I Y N D (d : ℤ) (e + 1) t S),
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S'
          (resT I Y N D (d : ℤ) hDm (e + 1) t h x) =
        resT I Y N D (d : ℤ) hDm e t h
          (red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e S x) :=
    fun S S' h x => GlobalTheory.T.thickening_restriction_compatible_opens R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) S) (D (e + 1) S') (D e S) (D e S')
      (hDβ e S).ge (hDβ e S').ge (hDm (e + 1) S S' h) (hDm e S S' h) x
  have hrr : ∀ (e : ℕ) (S S' S'' : Finset (Fin (m + 1))) (h : S ⊆ S') (h' : S' ⊆ S'')
      (x : Tm I Y N D (d : ℤ) e t S),
      resT I Y N D (d : ℤ) hDm e t h' (resT I Y N D (d : ℤ) hDm e t h x) =
        resT I Y N D (d : ℤ) hDm e t (h.trans h') x :=
    fun e S S' S'' h h' x => SecOnR.restrict_restrict _ _ _ x

  let σS : ∀ S, Tm I Y N D (d : ℤ) e t S := fun S => SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ (D e S))
  have hσS : ∀ (S S' : Finset (Fin (m + 1))) (h : S ⊆ S'),
      resT I Y N D (d : ℤ) hDm e t h (σS S) = σS S' :=
    fun S S' h => SecOn.restrict_ofSec σ (hDm e S S' h)

  have hlift : ∀ i, ∃ b : Tm I Y N D (d : ℤ) (e + 1) t {i},
      red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} b = σS {i} :=
    fun i => (GlobalTheory.T.thickening_affine_preimage R I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i})
      (hDa (e + 1) {i} (Finset.singleton_nonempty i))).1 (σS {i})
  choose b hb using hlift
  obtain ⟨b', hb'0, hb'c⟩ := hc
    (fun i j => resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) -
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j))
    (fun i j => by
      rw [map_sub, hres, hres, hb, hb, hσS, hσS, sub_self])
    (fun i j k => by
      simp only [map_sub, hrr]
      abel)

  have hf : ∀ i j, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i - b' i) =
      resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j - b' j) := fun i j => by
    rw [map_sub, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.1 (hb'c i j)
  have hfr : ∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i}
      (b i - b' i) = σS {i} := fun i => by rw [map_sub, hb, hb'0, sub_zero]

  obtain ⟨τ, hτ, -⟩ := SecOnR.existsUnique_glue (toR I Y (e + 1)) (M := pw (N (e + 1)) ((d : ℤ) * t))
    (V := ⊤) (fun i => D (e + 1) {i}) (fun _ => le_top) (hDc (e + 1)).ge (fun i => b i - b' i)
    (fun i j => by
      have hij : D (e + 1) {i} ⊓ D (e + 1) {j} ≤ D (e + 1) {i, j} := by
        rw [show ({i, j} : Finset (Fin (m + 1))) = insert i {j} from rfl, hDi (e + 1) {j} i,
          inf_comm]
      have h1 := congrArg (SecOnR.restrict (toR I Y (e + 1)) (pw (N (e + 1)) ((d : ℤ) * t)) hij)
        (hf i j)
      exact (SecOnR.restrict_restrict _ _ _ _).symm.trans
        (h1.trans (SecOnR.restrict_restrict _ _ _ _)))
  let σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)) := SecOnR.topEquiv _ _ τ
  have hτσ : τ = SecOnR.of _ _ _ (GlobalTheory.LB.ofSec σ' ⊤) :=
    ((SecOn.topEquiv (pw (N (e + 1)) ((d : ℤ) * t))).symm_apply_apply τ).symm
  refine ⟨σ', secMaps_of_cover (hLp e).1 (LB.isLB_pull (hLp (e + 1)).1 (β e)) _ (hLp e).2
    (fun i => D e {i}) (hDc e) σ (secPull σ' (β e)) fun i => ?_⟩
  refine congr_ofSec_of_redL I Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
    (fun e => pullPow (v e) ((d : ℤ) * t)) hLp e (D (e + 1) {i}) (D e {i}) (hDβ e {i}).ge σ' σ ?_
  have h2 : SecOnR.of (toR I Y (e + 1)) _ _ (GlobalTheory.LB.ofSec σ' (D (e + 1) {i})) = b i - b' i := by
    rw [← hτ i, hτσ]
    exact (SecOn.restrict_ofSec σ' le_top).symm
  rw [h2]
  exact hfr i

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_lift_projective_embedding_compatible : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℕ) (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))) (hs : VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s) (D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens) (hD0 : ∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) (hDβ : ∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) (hDm : ∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) (hDi : ∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) (hDc : ∀ e, ⨆ i, D e {i} = ⊤) (hDa : ∀ e S, S.Nonempty → IsAffineOpen (D e S)) (t : ℤ) (e : ℕ), (∀ (c : ∀ i j : Fin (m + 1), Tm I Y N D (d : ℤ) (e + 1) t {i, j}), (∀ i j, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i, j} (c i j) = 0) → (∀ i j k, resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ij i j k) (c i j) + resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_jk i j k) (c j k) = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_triple_ik i j k) (c i k)) → ∃ b : ∀ i, Tm I Y N D (d : ℤ) (e + 1) t {i}, (∀ i, red I Y N D β hβ v hN (fun e S => (hDβ e S).ge) ((d : ℤ) * t) e {i} (b i) = 0) ∧ ∀ i j, c i j = resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_left i j) (b i) - resT I Y N D (d : ℤ) hDm (e + 1) t (sub_pair_right i j) (b j)) → ∀ σ : LB.Sec (pw (N e) ((d : ℤ) * t)), ∃ σ' : LB.Sec (pw (N (e + 1)) ((d : ℤ) * t)), SecMaps (pullPow (v e) ((d : ℤ) * t)) σ (secPull σ' (β e)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.lift_of_cech_pairs
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option maxHeartbeats 1000000 in

theorem exists_uniform_lift : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  intro R _ _ I Y β hβ hP N v hN d hd m s hs
  obtain ⟨g, ρ, hρ⟩ : ∃ (g : ℕ) (ρ : Fin g → R), Ideal.span (Set.range ρ) = I := by
    obtain ⟨S, hS⟩ := (IsNoetherian.noetherian I : I.FG)
    refine ⟨S.card, fun k => (S.equivFin.symm k : R), ?_⟩
    rw [← hS]
    congr 1
    ext x
    simp only [Set.mem_range, Finset.mem_coe]
    exact ⟨fun ⟨k, hk⟩ => hk ▸ (S.equivFin.symm k).2, fun hx => ⟨S.equivFin ⟨x, hx⟩, by simp⟩⟩
  subst hρ
  obtain ⟨D, hD0, hDβ, hDm, hDi, hDc, hDa⟩ :=
    GlobalTheory.T.thickening_very_ample_opens_exist R _ Y β hβ (pw (N 0) (d : ℤ)) m s (isLB_pw (hN 0).1 _) hs
  obtain ⟨sh, hsh0, hshp, hshu⟩ := GlobalTheory.T.formal_lift_very_ample_sections R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
  have hc : ∀ e S, OperatorsCommute (ι := Fin (m + 1)) (R := R)
      (A := fun t => Tm _ Y N D (d : ℤ) e t S) fun j t => mulT _ Y N D (d : ℤ) e t S (sh e j S) :=
    fun e S i j t a => mulT_comm _ Y N D (d : ℤ) e t S (sh e i S) (sh e j S) a
  have hloc := GlobalTheory.T.formal_lift_sections_nonvanishing R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  have hDβ' : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S := fun e S => (hDβ e S).ge
  have h_pres : ∀ e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) (e + 1) t S),
      S.Nonempty → red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S' (resT _ Y N D (d : ℤ) hDm (e + 1) t h a) =
        resT _ Y N D (d : ℤ) hDm e t h (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) :=
    fun e t S S' h a _ => GlobalTheory.T.thickening_restriction_compatible_opens R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S)
      (D (e + 1) S') (D e S) (D e S') (hDβ' e S) (hDβ' e S') (hDm (e + 1) S S' h)
      (hDm e S S' h) a
  have h_mp : ∀ j e t (S : Finset (Fin (m + 1))) (a : Tm _ Y N D (d : ℤ) (e + 1) t S), S.Nonempty →
      red _ Y N D β hβ v hN hDβ' ((d : ℤ) * (t + 1)) e S (mulT _ Y N D (d : ℤ) (e + 1) t S (sh (e + 1) j S) a) =
        mulT _ Y N D (d : ℤ) e t S (sh e j S) (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S a) := by
    intro j e t S a hS
    have h1 := GlobalTheory.T.thickening_cech_cover_compatible R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * t)
      (d : ℤ) ((d : ℤ) * (t + 1)) (by ring) e S ((SecOnR.of _ _ _).symm a) (sh (e + 1) j S)
    rw [hshp e j S hS] at h1
    exact h1
  have h_mres : ∀ j e t (S S' : Finset (Fin (m + 1))) (h : S ⊆ S') (a : Tm _ Y N D (d : ℤ) e t S), S.Nonempty →
      resT _ Y N D (d : ℤ) hDm e (t + 1) h (mulT _ Y N D (d : ℤ) e t S (sh e j S) a) -
        mulT _ Y N D (d : ℤ) e t S' (sh e j S') (resT _ Y N D (d : ℤ) hDm e t h a) ∈
          Ideal.span (Set.range ρ) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e (t + 1) S')) :=
    fun j e t S S' h a hS => GlobalTheory.T.formal_lift_sections_generate R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa
      sh hsh0 hshp hshu j e t S S' h a hS
  have h_G3 : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Function.Surjective (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) ∧
        LinearMap.ker (red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S) = Ideal.span (Set.range ρ) ^ (e + 1) • ⊤ :=
    fun e t S hS => GlobalTheory.T.thickening_affine_preimage R _ Y β hβ (fun e => pw (N e) ((d : ℤ) * t))
      (fun e => pullPow (v e) ((d : ℤ) * t))
      (fun e => ⟨isLB_pw (hN e).1 _, pullPow_isGen (v e) _ (hN e).2⟩) e (D (e + 1) S) (D e S)
      (hDβ e S) (hDa (e + 1) S hS)
  have h_kill : ∀ e t (S : Finset (Fin (m + 1))), S.Nonempty →
      Ideal.span (Set.range ρ) ^ (e + 1) • (⊤ : Submodule R (Tm _ Y N D (d : ℤ) e t S)) = ⊥ :=
    fun e t S _ => GlobalTheory.T.ideal_power_annihilates_sections R _ Y e _ _
  have h_bij : ∀ i e t (S : Finset (Fin (m + 1))), i ∈ S → Function.Bijective (mulT _ Y N D (d : ℤ) e t S (sh e i S)) := by
    intro i e t S hi
    obtain ⟨y, hy⟩ := hshu e i S hi
    exact GlobalTheory.T.thickening_twisted_section_transition R _ Y β hβ N v hN (d : ℤ) (Fin (m + 1)) D e t S (sh e i S) y hy
  have h_one : ∀ e (i : Fin (m + 1)), red _ Y N D β hβ v hN hDβ' ((d : ℤ) * 0) e {i} (oneT _ Y N D (d : ℤ) (e + 1) {i}) =
      oneT _ Y N D (d : ℤ) e {i} :=
    fun e i => GlobalTheory.T.thickening_cech_restriction_commutes R _ Y β hβ N v hN (Fin (m + 1)) D hDβ' ((d : ℤ) * 0) (mul_zero _) e {i}
  have h_fin := GlobalTheory.T.formal_lift_closed_embedding R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa sh hsh0 hshp hshu hc
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.uniform_first_cohomology_kernels_exist (Fin (m + 1)) R g ρ (Tm _ Y N D (d : ℤ))
    (fun e t S S' h => resT _ Y N D (d : ℤ) hDm e t h)
    (fun e t S => red _ Y N D β hβ v hN hDβ' ((d : ℤ) * t) e S)
    (fun j e t S => mulT _ Y N D (d : ℤ) e t S (sh e j S))
    (fun e i => oneT _ Y N D (d : ℤ) e {i}) hc
    (fun e t S h a => SecOnR.restrict_self _ _ _)
    (fun e t S S' S'' h h' a => SecOnR.restrict_restrict _ _ _ _)
    h_pres h_mp h_mres (fun e t S hS => (h_G3 e t S hS).1) (fun e t S hS => (h_G3 e t S hS).2)
    h_kill h_bij hloc.1 hloc.2 h_one h_fin
  refine ⟨t₀.toNat, fun t ht D' hD' e σ => ?_⟩
  subst hD'
  exact GlobalTheory.T.formal_lift_projective_embedding_compatible R _ Y β hβ N v hN d m s hs D hD0 hDβ hDm hDi hDc hDa (t : ℤ) e
    (fun c hc0 hcoc => ht₀ t (by omega) e c hc0 hcoc) σ

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_line_bundle_very_ample_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift
end
