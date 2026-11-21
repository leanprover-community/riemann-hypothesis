import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TransitionFramesPushOpenImmersionImage
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAmpleCechLineBundleDisjointUnionPushforward
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLocalBasisAlong
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTripleGlueTwoOpens

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem lin_of_isEmpty {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} [hT : IsEmpty T'.left]
    (h : T' ⟶ T) {n : ℕ} (b : Fin n → LB.Sec (LPow G L (N : ℤ) T)) (c : Fin n → Γ(T'.left, ⊤))
    (s : LB.Sec (LPow G L (N : ℤ) T')) : Lin G L N h b c s := by
  intro z
  exact isEmptyElim ((fst T' G).left z)

theorem isEmpty_of_eq_bot {Z : Scheme.{0}} {U : Z.Opens} (h : U = ⊥) : IsEmpty U.toScheme := by
  subst h
  exact ⟨fun x => by simpa using x.2⟩

theorem subsingleton_sections_of_isEmpty {X : Scheme.{0}} [IsEmpty X] : Subsingleton Γ(X, ⊤) := by
  refine CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty ?_)
  ext x
  exact isEmptyElim x

open GlobalTheory.LN ReciprocityTheory.ChartRestriction.G.Out in

theorem trans_of_inf_eq_bot {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) {n : ℕ} (r s : ℤ) {U V : Z.Opens}
    (hUV : U ⊓ V = ⊥) (thU : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk U.ι)))
    (thV : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk V.ι)))
    (bU : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk U.ι))) (bV : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk V.ι)))
    (g : Γ(Z, U ⊓ V)) :
    ∃ (c : Γ((U ⊓ V).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((U ⊓ V).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => thU) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        (fun _ : Fin 1 => thV) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk U.ι)
        (fun _ : Fin 1 => bU k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (U ⊓ V).ι ⟶ Over.mk V.ι)
        bV (fun k' => M.val k k') t) ∧
    (U ⊓ V).topIso.inv.hom g = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val := by
  have hE : IsEmpty (U ⊓ V).toScheme := isEmpty_of_eq_bot hUV
  have := subsingleton_sections_of_isEmpty (X := (U ⊓ V).toScheme)
  have sec : ∀ M : ℕ, LB.Sec (LPow G L (M : ℤ) (Over.mk (U ⊓ V).ι)) := fun M =>
    { f := fun _ => 0
      compat := fun _ _ => fn_ext fun y _ => (hE.false ((fst (Over.mk (U ⊓ V).ι) G).left y)).elim }
  refine ⟨1, 1, ⟨sec 1, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _, lin_of_isEmpty (hT := hE) G L 1 _ _ _ _⟩,
    fun k => ⟨sec N, lin_of_isEmpty (hT := hE) G L N _ _ _ _, lin_of_isEmpty (hT := hE) G L N _ _ _ _⟩,
    Subsingleton.elim _ _⟩

theorem hasFrames_sumLB : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  intro Z G L N A B n r s hAB hA hB
  obtain ⟨thA, bA, hAt, hAb⟩ := hA
  obtain ⟨thB, bB, hBt, hBb⟩ := hB
  refine ⟨fun | .inl i => thA i | .inr j => thB j, fun | .inl i => bA i | .inr j => bB j, ?_, ?_⟩
  · rintro (i | i) (j | j)
    · exact hAt i j
    · exact trans_of_inf_eq_bot G L N r s (hAB i j) (thA i) (thB j) (bA i) (bB j) _
    · exact trans_of_inf_eq_bot G L N r s (by rw [inf_comm]; exact hAB j i) (thB i) (thA j) (bB i) (bA j) _
    · exact hBt i j
  · rintro (i | i) W _ _ _ hW χ hχ
    · exact hAb i W hW χ hχ
    · exact hBb i W hW χ hχ

end GlobalTheory.ModelSum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFrames_disjointUnionCechData : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A B : LB Z) (n : ℕ) (r s : ℤ), (∀ i j, A.U i ⊓ B.U j = ⊥) → HasFrames G L N A n r s → HasFrames G L N B n r s → HasFrames G L N (sumLB A B) n r s := by
  atlas_forward_decl GlobalTheory.ModelSum.hasFrames_sumLB
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

def noTraitZero {X : Scheme.{0}} (M : LB X) : M.Sec := ⟨fun _ => 0, by simp⟩

theorem noTrait_gs_zero {Y X : Scheme.{0}} (r : Y ⟶ X) (y : Y) (U : X.Opens) : gs r y U 0 = 0 := by
  unfold gs
  split_ifs <;> simp

theorem lin_noTraitZero {S : Scheme.{0}} (G : Over S) (L : LB G.left) (N : ℕ) {T T' : Over S} (h : T' ⟶ T) {n : ℕ}
    (c : Fin n → Γ(T'.left, ⊤)) : GlobalTheory.LN.Lin G L N h (fun _ => noTraitZero _) c (noTraitZero _) := by
  intro z J _
  refine (noTrait_gs_zero _ _ _).trans (Finset.sum_eq_zero fun i _ => ?_).symm
  exact (congrArg _ (noTrait_gs_zero _ _ _)).trans (mul_zero _)

theorem noTrait_exists_gl_det_eq {R : Type*} [CommRing R] {n : ℕ} (hn : 1 ≤ n) (u : Rˣ) :
    ∃ M : GL (Fin n) R, Matrix.GeneralLinearGroup.det M = u := by
  have hd : (Matrix.diagonal (Function.update (fun _ : Fin n => (1 : R)) ⟨0, hn⟩ u.val)).det = u.val := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  refine ⟨Matrix.GeneralLinearGroup.mk'' _ (by rw [hd]; exact u.isUnit), Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  exact hd

theorem hasFrames_rank_of_isEmpty (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ)
    (hn : 1 ≤ n') (hZ : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z))
    (h : HasFrames G L N A n r s) : HasFrames G L N A n' r s := by
  obtain ⟨th, b, h₁, -⟩ := h
  refine ⟨th, fun _ _ => noTraitZero _, fun i j => ?_, fun i W _ _ _ hW χ _ => ((hZ W hW).false (χ ≫ (A.U i).ι)).elim⟩
  obtain ⟨c, M, h₂, -, h₃⟩ := h₁ i j
  obtain ⟨M', hM⟩ := noTrait_exists_gl_det_eq hn (Matrix.GeneralLinearGroup.det M)
  exact ⟨c, M', h₂, fun k => ⟨noTraitZero _, lin_noTraitZero G L N _ _, lin_noTraitZero G L N _ _⟩, by rw [hM]; exact h₃⟩

end GlobalTheory.ModelSum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n n' : ℕ) (r s : ℤ), 1 ≤ n' → (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → IsEmpty (Sp W ⟶ Z)) → HasFrames G L N A n r s → HasFrames G L N A n' r s := by
  atlas_forward_decl GlobalTheory.ModelSum.hasFrames_rank_of_isEmpty
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ModelSum

theorem exists_pull_LPow_sec {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (N : ℕ) {T T' : Over Z}
    (h : T' ⟶ T) (b : LB.Sec (Out.LPow G L (N : ℤ) T)) :
    ∃ b' : LB.Sec (Out.LPow G L (N : ℤ) T'), ∀ (Y : Scheme.{0}) (r : Y ⟶ (T' ⊗ G).left) (z : Y) (J), Good L z J →
      sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) b' r z J =
        sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (r ≫ (h ▷ G).left) z J := by
  have hu : (LB.oneGen L (Y := (T' ⊗ G).left)).IsGen := by
    intro (i : PEmpty → L.ι) (j : PEmpty → L.ι)
    simp [LB.oneGen, LB.LinComb, res]
    ext
    erw [Units.val_mul, Units.coe_map, Units.coe_map, Units.val_one, _root_.one_mul, map_one, map_one]
  have hf : FormEq (Sum.elim (fun _ : Fin 1 => (h ▷ G).left ≫ (snd T G).left)
      (PEmpty.elim : PEmpty → ((T' ⊗ G).left ⟶ G.left))) (Sum.elim (fun _ => (N : ℤ)) PEmpty.elim)
      (fun _ : Fin 1 => (snd T' G).left) (fun _ => (N : ℤ)) := by
    intro U _ f
    simp [Fintype.prod_sum_type]
  obtain ⟨b', hb'⟩ := exists_sec hL hf
    (pullMulSec (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) b (h ▷ G).left
      (LB.oneGen L (Y := (T' ⊗ G).left)) hu)
  refine ⟨b', fun Y r z J hJ => (hb' Y r z J hJ).trans ((sval_pullMulSec _ _ _ hu r z hJ).trans ?_)⟩
  rw [val_one, Units.val_one, _root_.mul_one]

theorem basisAlong_id_of_basisAlong : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  intro Z G L N n T T' h b hL hB
  choose b' hb' using fun i => exists_pull_LPow_sec G L hL N h (b i)
  have key : ∀ s c, GlobalTheory.LN.Lin G L N (𝟙 T') b' c s ↔ GlobalTheory.LN.Lin G L N h b c s := by
    intro s c
    have e : ∀ i (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) (b' i) ((𝟙 T') ▷ G).left z J =
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro i z J hJ
      rw [hb' i _ _ z J hJ]
      simp
    unfold GlobalTheory.LN.Lin
    refine forall_congr' fun z => forall_congr' fun J => imp_congr_right fun hJ => ?_
    simp only [e _ z J hJ]
  unfold GlobalTheory.LN.BasisAlong at hB ⊢
  refine ⟨b', fun s => ?_⟩
  obtain ⟨c, hc, hu⟩ := hB s
  exact ⟨c, (key s c).2 hc, fun c' hc' => hu c' ((key s c').1 hc')⟩

end GlobalTheory.ModelSum
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis : ∀ (Z : Scheme.{0}) (G : Over Z) (L : LB G.left) (N n : ℕ) (T T' : Over Z) (h : T' ⟶ T) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → GlobalTheory.LN.BasisAlong G L N h b → ∃ b' : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T'), GlobalTheory.LN.BasisAlong G L N (𝟙 T') b' := by
  first | exact @GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | exact GlobalTheory.ModelSum.basisAlong_id_of_basisAlong | (intros; apply GlobalTheory.ModelSum.basisAlong_id_of_basisAlong <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN.SecRank

theorem card_eq_of_basisAlong {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {T₁ T₂ T' : Over S} [Nontrivial Γ(T'.left, ⊤)] (h₁ : T' ⟶ T₁) (h₂ : T' ⟶ T₂) {n m : ℕ}
    {a : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T₁)} {b : Fin m → LB.Sec (Out.LPow G L (N : ℤ) T₂)}
    (ha : BasisAlong G L N h₁ a) (hb : BasisAlong G L N h₂ b) : n = m := by
  choose a' ha' _ using fun i => PolFrames.exists_pullSec G L N h₁ (a i)
  choose b' hb' _ using fun i => PolFrames.exists_pullSec G L N h₂ (b i)
  obtain ⟨l₁, s₁⟩ := (PolFrames.basisAlong_iff G L N h₁ hL ha').1 ha
  obtain ⟨l₂, s₂⟩ := (PolFrames.basisAlong_iff G L N h₂ hL hb').1 hb
  have e₁ := Module.finrank_eq_card_basis (Module.Basis.mk l₁ s₁.ge)
  have e₂ := Module.finrank_eq_card_basis (Module.Basis.mk l₂ s₂.ge)
  simpa using e₁.symm.trans e₂

theorem card_basis_eq_pow : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  intro _ hL R _ _ P N n b hN hb
  obtain ⟨V, hV, c, hc⟩ := hL.secBaseChangeAny (Sp R) P N hN (IsLocalRing.closedPoint R)
  have hV' : V = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    exact (IsLocalRing.specializes_closedPoint x).mem_open V.isOpen hV
  subst hV'
  let χ : Sp R ⟶ (⊤ : (Sp R).Opens).toScheme := (Sp R).topIso.inv
  choose c' hc' _ using fun i => PolFrames.exists_pullSec P.A P.L N (Out.homAt χ) (c i)
  have H := (PolFrames.basisAlong_iff P.A P.L N (Out.homAt χ) P.isLB hc').2 (hc R χ c' hc')
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R)) : Over (Sp R)).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  have key : ∀ (f : Sp R ⟶ Sp R) (hf : f = 𝟙 _) (T : Over (Sp R)) (h : Over.mk f ⟶ T)
      (d : Fin (N ^ P.g) → LB.Sec (Out.LPow P.A P.L (N : ℤ) T)), BasisAlong P.A P.L N h d → n = N ^ P.g := by
    rintro _ rfl T h d hd
    exact card_eq_of_basisAlong P.A P.L P.isLB N _ h hb hd
  refine key (Out.baseAt χ).hom ?_ _ (Out.homAt χ) c H
  exact (congrArg (χ ≫ ·) (Category.comp_id (⊤ : (Sp R).Opens).ι)).trans (Sp R).toIso_inv_ι

end GlobalTheory.LN.SecRank
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsLocalRing R] (P : Out.PolAV (Sp R)) (N n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L (N : ℤ) (Over.mk (𝟙 (Sp R))))), 1 ≤ N → GlobalTheory.LN.BasisAlong P.A P.L N (𝟙 _) b → n = N ^ P.g := by
  atlas_forward_decl GlobalTheory.LN.SecRank.card_basis_eq_pow
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.RankZero

section
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem top_le_wchart (ψ : Fin 0 → (Y ⟶ X)) (j : Fin 0 → L.ι) : (⊤ : Y.Opens) ≤ LB.wchart L ψ j :=
  fun _ _ => Set.mem_iInter.2 fun k => k.elim0

theorem exists_fn (hL : L.IsLB) (hε : ∀ k, ε k = 0) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ f : Γ(Y, ⊤), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hF : FormEq φ ε (Fin.elim0 : Fin 0 → (Y ⟶ X)) (Fin.elim0 : Fin 0 → ℤ) := by
    intro U _ h
    simp [hε]
  obtain ⟨s', hs'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_sec hL hF s
  refine ⟨(Y.presheaf.map (homOfLE (top_le_wchart (L := L) Fin.elim0 Fin.elim0)).op).hom (s'.f Fin.elim0),
    fun y J hJ => ?_⟩
  rw [← hs' Y (𝟙 Y) y J hJ, sval_of s' (𝟙 Y) y J Fin.elim0 (fun k => k.elim0)]
  exact (gs_res (𝟙 Y) y (top_le_wchart (L := L) Fin.elim0 Fin.elim0) trivial _).symm

theorem exists_sec_of_fn (hε : ∀ k, ε k = 0) (f : Γ(Y, ⊤)) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ y J, Good L y J → sval s (𝟙 Y) y J = gs (𝟙 Y) y ⊤ f := by
  have hle : ∀ j : K → L.ι, LB.wchart L φ j ≤ ⊤ := fun _ => le_top
  have h1 : ∀ y j j', trF (L := L) φ ε (𝟙 Y) y j j' = 1 := fun y j j' => by simp [trF, hε]
  refine ⟨⟨fun j => (Y.presheaf.map (homOfLE (hle j)).op).hom f, fun (j j' : K → L.ι) => fn_ext fun y hy => ?_⟩,
    fun y J hJ => (gs_res (𝟙 Y) y (hle _) (hJ.mem φ (𝟙 Y)) f)⟩
  have hg : gm (𝟙 Y) y ((L.LinComb φ ε).U j ⊓ (L.LinComb φ ε).U j') ((L.LinComb φ ε).g j j') = 1 :=
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2).trans (h1 y j j')
  rw [gs_mul (𝟙 Y) y _ hy, gs_unit (𝟙 Y) y _ hy, hg, Units.val_one, _root_.one_mul]
  exact ((gs_res (𝟙 Y) y inf_le_left hy _).trans (gs_res (𝟙 Y) y (hle j) hy.1 f)).trans
    ((gs_res (𝟙 Y) y inf_le_right hy _).trans (gs_res (𝟙 Y) y (hle j') hy.2 f)).symm

end

theorem eq_one_of_existsUnique {Γ : Type} [CommRing Γ] [Nontrivial Γ] {n : ℕ} (β : Fin n → Γ)
    (h : ∀ a : Γ, ∃! c : Fin n → Γ, a = ∑ i, c i * β i) : n = 1 := by
  let F : (Fin n → Γ) →ₗ[Γ] Γ :=
    { toFun := fun c => ∑ i, c i * β i
      map_add' := fun x y => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [_root_.mul_assoc] }
  have hF : ∀ c, F c = ∑ i, c i * β i := fun _ => rfl
  have hb : Function.Bijective F := by
    refine ⟨fun c c' hcc => ?_, fun a => ?_⟩
    · obtain ⟨d, -, hd⟩ := h (F c)
      exact (hd c (hF c)).trans (hd c' (hcc.trans (hF c'))).symm
    · obtain ⟨c, hc, -⟩ := h a
      exact ⟨c, (hF c).trans hc.symm⟩
  have e := (LinearEquiv.ofBijective F hb).finrank_eq
  simpa using e

theorem eq_one_of_bijective {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (hL : L.IsLB) (T : Over Z)
    [Nontrivial Γ(T.left, ⊤)] (hb : Function.Bijective (fst T G).left.appTop.hom) {n : ℕ}
    (b : Fin n → LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)) (H : GlobalTheory.LN.BasisAlong G L 0 (𝟙 _) b) : n = 1 := by
  have hpull : ∀ (x : Γ(T.left, ⊤)) (y : (T ⊗ G).left),
      gs (fst T G).left y ⊤ x = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom x) := fun x y => by
    have e := gs_pull (𝟙 _) (fst T G).left y ⊤ trivial x
    rw [Category.id_comp] at e
    exact e.symm
  have hρ : ∀ y : (T ⊗ G).left, ∃ ρ : Γ((T ⊗ G).left, ⊤) →+* (T ⊗ G).left.presheaf.stalk y,
      ∀ a, gs (𝟙 _) y ⊤ a = ρ a := fun y =>
    ⟨((T ⊗ G).left.presheaf.germ ((𝟙 (T ⊗ G).left) ⁻¹ᵁ ⊤) y trivial).hom.comp (Scheme.Hom.app (𝟙 (T ⊗ G).left) ⊤).hom,
      fun a => gs_eq _ y ⊤ trivial a⟩
  choose β' hβ' using fun i => exists_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ)) hL
    (fun _ => rfl) (b i)
  choose β hβ using fun i => hb.2 (β' i)
  have hR : ∀ (c : Fin n → Γ(T.left, ⊤)) (z : (T ⊗ G).left) (J : ((T ⊗ G).left ⟶ G.left) → L.ι), Good L z J →
      ∑ i, gs (fst T G).left z ⊤ (c i) * sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left)
        (ε := fun _ => ((0 : ℕ) : ℤ)) (b i) (𝟙 T ▷ G).left z J
        = gs (𝟙 _) z ⊤ ((fst T G).left.appTop.hom (∑ i, c i * β i)) := by
    intro c z J hJ
    obtain ⟨ρ, hρz⟩ := hρ z
    rw [MonoidalCategory.id_whiskerRight, Over.id_left]
    simp only [hβ' _ z J hJ, hpull, hρz, map_sum, map_mul, hβ]
  have hiff : ∀ (a : Γ(T.left, ⊤)) (c : Fin n → Γ(T.left, ⊤)) (s : LB.Sec (Out.LPow G L ((0 : ℕ) : ℤ) T)),
      (∀ y J, Good L y J → sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => ((0 : ℕ) : ℤ))
        s (𝟙 _) y J = gs (𝟙 _) y ⊤ ((fst T G).left.appTop.hom a)) →
      (GlobalTheory.LN.Lin G L 0 (𝟙 T) b c s ↔ a = ∑ i, c i * β i) := by
    intro a c s hs
    constructor
    · intro hl
      apply hb.1
      apply fn_ext
      intro z _
      obtain ⟨J, hJ, -⟩ := exists_good L hL z (Fin.elim0 : Fin 0 → ((T ⊗ G).left ⟶ G.left)) Fin.elim0
        (fun a => a.elim0) (fun k => k.elim0)
      rw [← hs z J hJ, hl z J hJ, hR c z J hJ]
    · rintro rfl z J hJ
      rw [hs z J hJ, hR c z J hJ]
  refine eq_one_of_existsUnique β (fun a => ?_)
  obtain ⟨s, hs⟩ := exists_sec_of_fn (L := L) (fun _ : Fin 1 => (snd T G).left) (fun _ => ((0 : ℕ) : ℤ))
    (fun _ => rfl) ((fst T G).left.appTop.hom a)
  obtain ⟨c, hc, hcu⟩ := H s
  exact ⟨c, (hiff a c s hs).1 hc, fun c' hc' => hcu c' ((hiff a c' s hs).2 hc')⟩

end GlobalTheory.RankZero

theorem GlobalTheory.basisAlong_zero_card : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  intro hG R _ _ P n b hB
  have : Nontrivial Γ((Over.mk (𝟙 (Sp R))).left, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  refine GlobalTheory.RankZero.eq_one_of_bijective P.A P.L P.isLB (Over.mk (𝟙 (Sp R))) ?_ b hB
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A) := by
    change IsIso (snd (𝟙_ (Over (Sp R))) P.A)
    rw [← CartesianMonoidalCategory.leftUnitor_hom]
    infer_instance
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left :=
    (inferInstance : IsIso ((Over.forget _).map (snd (Over.mk (𝟙 (Sp R))) P.A)))
  have e1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left = (snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom := by
    have h1 : (fst (Over.mk (𝟙 (Sp R))) P.A).left ≫ 𝟙 (Sp R) = _ := Over.w (fst (Over.mk (𝟙 (Sp R))) P.A)
    have h2 := Over.w (snd (Over.mk (𝟙 (Sp R))) P.A)
    exact (Category.comp_id _).symm.trans (h1.trans h2.symm)
  have hc : ((snd (Over.mk (𝟙 (Sp R))) P.A).left ≫ P.A.hom).appTop =
      P.A.hom.appTop ≫ (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    simp
  have : IsIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop := by
    exact (inferInstance : IsIso ((snd (Over.mk (𝟙 (Sp R))) P.A).left.app ⊤))
  rw [e1, hc, CommRingCat.hom_comp, RingHom.coe_comp]
  exact Function.Bijective.comp (asIso (snd (Over.mk (𝟙 (Sp R))) P.A).left.appTop).commRingCatIsoToRingEquiv.bijective
    (@hG _ P.A P.grp P.isAb)

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_basis_polarisation_power_zero_eq_one : Out.GlobalFnsSt → ∀ (R : Type) [CommRing R] [Nontrivial R] (P : Out.PolAV (Sp R)) (n : ℕ) (b : Fin n → LB.Sec (Out.LPow P.A P.L ((0 : ℕ) : ℤ) (Over.mk (𝟙 (Sp R))))), GlobalTheory.LN.BasisAlong P.A P.L 0 (𝟙 _) b → n = 1 := by
  atlas_forward_decl GlobalTheory.basisAlong_zero_card
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.AbLocusLocal

private theorem isProper_of_isPullback_of_pullback_snd {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper (pullback.snd f g)) : IsProper snd := by
  rw [← h.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.hom (pullback.snd f g)).2 H

private theorem isProper_pullback_snd_of_isPullback {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (H : IsProper snd) : IsProper (pullback.snd f g) := by
  rw [← h.isoPullback_inv_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper h.isoPullback.inv snd).2 H

private theorem isProper_snd_of_isPullback_of_isProper {A B C D : Scheme.{0}} {fst : A ⟶ B} {snd : A ⟶ C} {f : B ⟶ D}
    {g : C ⟶ D} (h : IsPullback fst snd f g) (hf : IsProper f) : IsProper snd :=
  isProper_of_isPullback_of_pullback_snd h inferInstance

theorem isProper_restrict_of_cover {X Z : Scheme.{0}} (p : X ⟶ Z) {I : Type} {Y X' : I → Scheme.{0}}
    (f : ∀ i, Y i ⟶ Z) [∀ i, IsOpenImmersion (f i)] (p' : ∀ i, X' i ⟶ Y i) (F : ∀ i, X' i ⟶ X)
    (h : ∀ i, IsPullback (F i) (p' i) p (f i)) (V : ∀ i, (Y i).Opens) (hV : ∀ i, IsProper (p' i ∣_ V i))
    (U : Z.Opens) (hle : ∀ i, Set.range ((V i).ι ≫ f i) ⊆ Set.range U.ι)
    (hc : ∀ z ∈ U, ∃ i, z ∈ Set.range ((V i).ι ≫ f i)) : IsProper (p ∣_ U) := by
  have hsq : ∀ i, IsPullback (((p' i) ⁻¹ᵁ V i).ι ≫ F i) (p' i ∣_ V i) p ((V i).ι ≫ f i) := fun i =>
    (isPullback_morphismRestrict (p' i) (V i)).flip.paste_horiz (h i)
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun i => U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨i, hi⟩ := hc (U.ι x) x.2
    exact ⟨i, by simpa [Scheme.Hom.coe_opensRange] using hi⟩
  · intro i
    let W : U.toScheme.Opens := U.ι ⁻¹ᵁ ((V i).ι ≫ f i).opensRange
    have hr : Set.range (W.ι ≫ U.ι) ⊆ Set.range ((V i).ι ≫ f i) := by
      rintro _ ⟨x, rfl⟩
      have hx : U.ι x.val ∈ ((V i).ι ≫ f i).opensRange := x.2
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hx
      exact hx
    let e := IsOpenImmersion.lift ((V i).ι ≫ f i) (W.ι ≫ U.ι) hr
    have he : e ≫ ((V i).ι ≫ f i) = W.ι ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
    have big := (isPullback_morphismRestrict (p ∣_ U) W).flip.paste_horiz (isPullback_morphismRestrict p U).flip
    rw [← he] at big
    have hw : ((((p ∣_ U) ⁻¹ᵁ W).ι ≫ (p ⁻¹ᵁ U).ι)) ≫ p = ((p ∣_ U) ∣_ W ≫ e) ≫ ((V i).ι ≫ f i) := by
      rw [big.w, Category.assoc]
    have sq : IsPullback ((hsq i).lift _ _ hw) ((p ∣_ U) ∣_ W) (p' i ∣_ V i) e := by
      refine IsPullback.of_right ?_ ((hsq i).lift_snd _ _ hw) (hsq i)
      rw [(hsq i).lift_fst]
      exact big
    exact isProper_snd_of_isPullback_of_isProper sq (hV i)

private theorem mem_abLocus_of_map_mem_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y) (hy : g y ∈ abLocus B) :
    y ∈ abLocus A := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x, rfl⟩ := hs
  have big := (IsPullback.of_hasPullback A.hom s).paste_horiz h
  exact isProper_of_isPullback_of_pullback_snd big (hy K (s ≫ g) ⟨x, by rw [Scheme.Hom.comp_apply]⟩)

private theorem map_mem_abLocus_of_isPullback {Y Z : Scheme.{0}} {A : Over Y} {B : Over Z} {g : Y ⟶ Z}
    [IsOpenImmersion g] {φ : A.left ⟶ B.left} (h : IsPullback φ A.hom B.hom g) (y : Y)
    (hy : y ∈ abLocus A) : g y ∈ abLocus B := by
  simp only [abLocus, Set.mem_setOf_eq] at hy ⊢
  intro K _ _ s hs
  obtain ⟨x0, hx0⟩ := hs
  have hr : Set.range s ⊆ Set.range g := by
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x x0, hx0]
    exact ⟨y, rfl⟩
  have hs' : IsOpenImmersion.lift g s hr ≫ g = s := IsOpenImmersion.lift_fac g s hr
  have big := (IsPullback.of_hasPullback A.hom (IsOpenImmersion.lift g s hr)).paste_horiz h
  rw [hs'] at big
  have hy' : y ∈ Set.range (IsOpenImmersion.lift g s hr) := by
    refine ⟨x0, g.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hs', hx0]
  exact isProper_pullback_snd_of_isPullback big (hy K _ hy')

theorem abOpen_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  intro E _ _ _ H Z t I Y f u m hf hc hab
  unfold AbOpen at hab ⊢
  choose V hVs hVp using hab
  have hpb : ∀ i, IsPullback (m i).φ (u i).G.hom t.G.hom (f i) := fun i => (m i).cart.1
  refine ⟨⨆ i, ((V i).ι ≫ f i).opensRange, ?_, ?_⟩
  · ext z
    simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, Scheme.Hom.coe_opensRange]
    constructor
    · rintro ⟨i, v, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact map_mem_abLocus_of_isPullback (hpb i) _ (by rw [← hVs i]; exact v.2)
    · intro hz
      obtain ⟨i, y, rfl⟩ := hc z
      have hy := mem_abLocus_of_map_mem_of_isPullback (hpb i) y hz
      rw [← hVs i] at hy
      exact ⟨i, ⟨y, hy⟩, rfl⟩
  · refine isProper_restrict_of_cover t.G.hom f (fun i => (u i).G.hom) _ hpb V hVp _ ?_ ?_
    · intro i z hz
      rw [Scheme.Opens.range_ι]
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, by rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange]; exact hz⟩
    · intro z hz
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
      rw [← SetLike.mem_coe, Scheme.Hom.coe_opensRange] at hi
      exact ⟨i, hi⟩

end GlobalTheory.AbLocusLocal
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, AbOpen (u i).G) → AbOpen t.G := by
  first | exact @GlobalTheory.AbLocusLocal.abOpen_of_cover | exact GlobalTheory.AbLocusLocal.abOpen_of_cover | (intros; apply GlobalTheory.AbLocusLocal.abOpen_of_cover <;> assumption)
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory

theorem splitFibre_of_isOpenImmersion {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsOpenImmersion f] (G : Over Z) [GrpObj G]
    (G' : Over Y) [GrpObj G'] (φ : G'.left ⟶ G.left) (hφ : IsGrpPullback G' G f φ) (h : SplitFib G') (y : Y) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (Z.residueField (f y)) k), FiniteDimensional (Z.residueField (f y)) k ∧
      Algebra.IsSeparable (Z.residueField (f y)) k ∧ ∃ S : SplitExt (Sp k),
        S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫
          Z.fromSpecResidueField (f y))).obj G) := by
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := h y
  let ε : Z.residueField (f y) ≃+* Y.residueField y := (asIso (f.residueFieldMap y)).commRingCatIsoToRingEquiv
  let A : Algebra (Z.residueField (f y)) k :=
    ((algebraMap (Y.residueField y) k).comp (f.residueFieldMap y).hom).toAlgebra
  have hc : (algebraMap (Z.residueField (f y)) k).comp (ε.symm : Y.residueField y →+* Z.residueField (f y)) =
      ((RingEquiv.refl k : k ≃+* k) : k →+* k).comp (algebraMap (Y.residueField y) k) := by
    ext a
    exact congrArg (algebraMap (Y.residueField y) k) (ε.apply_symm_apply a)
  refine ⟨k, inferInstance, A, Module.Finite.of_equiv_equiv ε.symm (RingEquiv.refl k) hc,
    Algebra.IsSeparable.of_equiv_equiv ε.symm (RingEquiv.refl k) hc, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Y.fromSpecResidueField y) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) ≫ Z.fromSpecResidueField (f y) := by
    have a₁ : Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField (f y)) k)) =
        Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫ Spec.map (f.residueFieldMap y) := by
      rw [← Spec.map_comp]
      rfl
    rw [a₁, Category.assoc, Category.assoc, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rw [← key]
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  have : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y)).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₀ := isGt_of_iso ((Over.pullback _).mapIso e) hGt
  have : IsMonHom (pullCompIso (Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) k)) ≫
      Y.fromSpecResidueField y) f G).symm.hom := by
    show IsMonHom (pullCompIso _ _ _).inv
    infer_instance
  exact isGt_of_iso (pullCompIso _ f G).symm h₀

theorem splitFib_of_openCover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  intro E _ _ _ H Z t I Y f u m ho hc hs z
  obtain ⟨i, y, rfl⟩ := hc z
  have := ho i
  exact splitFibre_of_isOpenImmersion (f i) t.G (u i).G _ (m i).cart (hs i) y

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibresSplit_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, SplitFib (u i).G) → SplitFib t.G := by
  atlas_forward_decl GlobalTheory.splitFib_of_openCover
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ThetaLocal

open GlobalTheory.AbLocusPull

variable {X X' : Scheme.{0}}

theorem fn_ext_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    {a b : Γ(X, U)} (h : ∀ x, F x ∈ U → gs F x U a = gs F x U b) : a = b := by
  have := F.isIso_app U hU
  apply (ConcreteCategory.bijective_of_isIso (F.app U)).1
  refine fn_ext fun x hx => ?_
  have e₁ := gs_pull (𝟙 X') F x U hx a
  have e₂ := gs_pull (𝟙 X') F x U hx b
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h x hx).trans e₂.symm)

theorem exists_fn_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    (b : Γ(X', F ⁻¹ᵁ U)) : ∃ a : Γ(X, U), ∀ x, F x ∈ U → gs F x U a = gs (𝟙 X') x _ b := by
  have := F.isIso_app U hU
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F.app U)).2 b
  refine ⟨a, fun x hx => ?_⟩
  have e₁ := gs_pull (𝟙 X') F x U hx a
  rw [Category.id_comp] at e₁
  exact e₁.symm

theorem exists_secOn_push {F : X' ⟶ X} [IsOpenImmersion F] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hr : W ≤ F.opensRange) (hW : F ⁻¹ᵁ W ≤ W')
    {θ' : ∀ k, Γ(X', W' ⊓ L'.U k)} (hθ' : θ' ∈ secOn L' W') :
    ∃ θ ∈ secOn L W, ∀ x, F x ∈ W → ∀ j k, F x ∈ L.U j → x ∈ X'.basicOpen (θ' k) → F x ∈ X.basicOpen (θ j) := by
  obtain ⟨w, hw⟩ := hw
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', F x ∈ W → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) =
        (gm F x (L.U j ⊓ L.U j') (L.g j j')).val * ((gw w (𝟙 X') x j' k').val * gs (𝟙 X') x _ (θ' k')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ' (𝟙 X') x k k' (hW hx) hk hk', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul]
    congr 2
    rw [mul_right_comm, inv_mul_cancel_right]
  have ex : ∀ j, ∃ a : Γ(X, W ⊓ L.U j), ∀ x k, F x ∈ W → F x ∈ L.U j → x ∈ L'.U k →
      gs F x _ a = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
    intro j
    let O : L'.ι → X'.Opens := fun k => F ⁻¹ᵁ W ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ k, O k ≤ W' ⊓ L'.U k := fun k x hx => ⟨hW hx.1, hx.2.2⟩
    let u : ∀ k, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun k => w.s (fun _ => j, k)
    let a : ∀ k, Γ(X', O k) := fun k => resG X' inf_le_right (u k).val * resG X' (le k) (θ' k)
    have va : ∀ x k, x ∈ O k → gs (𝟙 X') x _ (a k) = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
      intro x k hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (F ⁻¹ᵁ (W ⊓ L.U j)) O (fun k x hx => ⟨hx.1, mem_pull.1 hx.2.1⟩)
      (fun x hx => (exists_chart hL' x).imp fun k hk => ⟨hx.1, mem_pull.2 hx.2, hk⟩) a (fun k k' x hk hk' => by
        rw [va x k hk, va x k' hk', rel x j j k k' hk.1 (mem_pull.1 hk.2.1) (mem_pull.1 hk.2.1) hk.2.2 hk'.2.2,
          gm_self hL F x (mem_pull.1 hk.2.1), Units.val_one, _root_.one_mul])
    obtain ⟨c, hc⟩ := exists_fn_of_isOpenImmersion F (inf_le_left.trans hr) b
    refine ⟨c, fun x k hx hj hk => ?_⟩
    have hm : x ∈ O k := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hc x ⟨hx, hj⟩).trans ((hb x k hm).trans (va x k hm))
  choose θ hθ using ex
  refine ⟨θ, fun j j' => fn_ext_of_isOpenImmersion F (inf_le_left.trans (inf_le_left.trans hr)) fun x hx => ?_,
    fun x hx j k hj hk => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit F x (L.U j ⊓ L.U j') ⟨hx.1.2, hx.2⟩, hθ j x k hx.1.1 hx.1.2 hk, hθ j' x k hx.1.1 hx.2 hk]
    exact rel x j j' k k hx.1.1 hx.1.2 hx.2 hk hk
  · have hm : x ∈ W' ⊓ L'.U k := X'.basicOpen_le _ hk
    refine (isUnit_gs_iff F x (W ⊓ L.U j) ⟨hx, hj⟩ _).1 ?_
    rw [hθ j x k hx hj hm.2]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X') x _ hm _).2 hk)

theorem hasTheta_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  intro E _ _ _ H Z t I Y f u m hf hc hu z
  obtain ⟨i, y, rfl⟩ := hc z
  have := hf i
  have h := (m i).cart.1
  have : IsOpenImmersion (m i).cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := (m i).lin
  have sq : ∀ x, t.G.hom ((m i).cm.F x) = f i ((u i).G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hy, θ', hθ', hne⟩ := hu i y
  have hr : t.G.hom ⁻¹ᵁ (f i ''ᵁ V) ≤ (m i).cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : (m i).cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (f i ''ᵁ V)) ≤ (u i).G.hom ⁻¹ᵁ V := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = (u i).G.hom x := (f i).isOpenEmbedding.injective (e.trans (sq x))
    show (u i).G.hom x ∈ V
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := exists_secOn_push t.PP.isLB (u i).PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨f i ''ᵁ V, ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨x, k, hx, hk⟩ := hne y' hy'
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB ((m i).cm.F x)
  refine ⟨(m i).cm.F x, j, (sq x).trans (congrArg _ hx), hb x ⟨y', hy', ?_⟩ j k hj hk⟩
  exact ((sq x).trans (congrArg _ hx)).symm

end GlobalTheory.ThetaLocal

end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.hasTheta_of_cover | exact GlobalTheory.ThetaLocal.hasTheta_of_cover | (intros; apply GlobalTheory.ThetaLocal.hasTheta_of_cover <;> assumption)
end

section
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ProjSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in
private theorem isImmersion_coprod_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y')
    [IsImmersion f] [IsImmersion g] : IsImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{0, 0} X' Y') ?_
  rintro (⟨⟩ | ⟨⟩)
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inl)
    have h := (isPullback_inl_inl_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance
  · change IsImmersion (pullback.snd (coprod.map f g) coprod.inr)
    have h := (isPullback_inr_inr_coprodMap f g).flip
    rw [← Iso.inv_hom_id_assoc h.isoPullback (pullback.snd _ _), h.isoPullback_hom_snd]
    infer_instance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.ProjSpace.isQProjOver_of_isCompl : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0})
    (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ →
    IsCompl (Set.range f₁) (Set.range f₂) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₁ ≫ s) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (f₂ ≫ s) →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver s := by
  intro R _ X X₁ X₂ f₁ f₂ s h₁ h₂ hc q₁ q₂
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at q₁ q₂ ⊢
  obtain ⟨N₁, i₁, hi₁, hq₁, e₁⟩ := q₁
  obtain ⟨N₂, i₂, hi₂, hq₂, e₂⟩ := q₂
  have hP := _root_.GlobalTheory.ProjSpace.isProjOver_coprodDesc (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₁)
    (_root_.GlobalTheory.ProjSpace.isProjOver_pspace_str R N₂)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver at hP
  obtain ⟨M, j, hj, ej⟩ := hP
  have hc' : IsCompl f₁.opensRange f₂.opensRange :=
    ⟨disjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.inf_eq_bot)),
      codisjoint_iff.mpr (SetLike.coe_injective (by simpa using hc.sup_eq_top))⟩
  obtain ⟨hX⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl f₁ f₂ hc'
  let e : X₁ ⨿ X₂ ≅ X := (coprodIsCoprod X₁ X₂).coconePointUniqueUpToIso hX
  have he₁ : coprod.inl ≫ e.hom = f₁ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.left⟩
  have he₂ : coprod.inr ≫ e.hom = f₂ :=
    (coprodIsCoprod X₁ X₂).comp_coconePointUniqueUpToIso_hom hX ⟨WalkingPair.right⟩
  have hcomp : (e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M = s := by
    rw [Category.assoc, Category.assoc, ej, Iso.inv_comp_eq]
    apply coprod.hom_ext
    · rw [coprod.inl_map_assoc, coprod.inl_desc, ← Category.assoc, he₁, e₁]
    · rw [coprod.inr_map_assoc, coprod.inr_desc, ← Category.assoc, he₂, e₂]
  haveI := isImmersion_coprod_map i₁ i₂
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R M
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₁
  haveI := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N₂
  haveI : CompactSpace X₁ := (quasiCompact_iff_compactSpace (f₁ ≫ s)).mp (by rw [← e₁]; infer_instance)
  haveI : CompactSpace X₂ := (quasiCompact_iff_compactSpace (f₂ ≫ s)).mp (by rw [← e₂]; infer_instance)
  haveI : CompactSpace X := ⟨by
    rw [← Set.top_eq_univ, ← hc.sup_eq_top]
    exact (isCompact_range f₁.continuous).union (isCompact_range f₂.continuous)⟩
  haveI : QuasiCompact s := (quasiCompact_iff_compactSpace s).mpr inferInstance
  haveI : QuasiCompact ((e.inv ≫ coprod.map i₁ i₂ ≫ j) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M) := by
    rw [hcomp]; infer_instance
  exact ⟨M, e.inv ≫ coprod.map i₁ i₂ ≫ j, inferInstance,
    QuasiCompact.of_comp _ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str R M), hcomp⟩

end GlobalTheory.ProjSpace
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_of_isCompl_openImmersions : ∀ (R : Type) [CommRing R] (X X₁ X₂ : Scheme.{0}) (f₁ : X₁ ⟶ X) (f₂ : X₂ ⟶ X) (s : X ⟶ Sp R), IsOpenImmersion f₁ → IsOpenImmersion f₂ → IsCompl (Set.range f₁) (Set.range f₂) → IsQProjOver (f₁ ≫ s) → IsQProjOver (f₂ ≫ s) → IsQProjOver s := by
  atlas_forward_decl GlobalTheory.ProjSpace.isQProjOver_of_isCompl
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.GenTrait

theorem charZero_functionField (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [CharZero W]
    (f : Sp W ⟶ Z) : CharZero Z.functionField := by
  have h1 : CharZero Γ(Z, ⊤) :=
    RingHom.charZero (f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom).hom
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨genericPoint Z, trivial⟩⟩
  exact charZero_of_injective_ringHom (Z.germToFunctionField_injective ⊤)

theorem exists_trait_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  intro Z _ W _ _ _ f
  have := charZero_functionField Z W f
  refine ⟨PowerSeries Z.functionField, inferInstance, inferInstance, inferInstance, ?_,
    spMap (algebraMap Z.functionField (PowerSeries Z.functionField)) ≫
      Z.fromSpecStalk (genericPoint Z), fun y => ?_⟩
  · exact ⟨inferInstance, by rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance,
      algebraRat.charZero _⟩
  · rw [Scheme.Hom.comp_apply]
    have hy : ∀ p : PrimeSpectrum Z.functionField, p = IsLocalRing.closedPoint Z.functionField :=
      fun p => Subsingleton.elim _ _
    exact (congrArg (Z.fromSpecStalk (genericPoint Z)) (hy _)).trans
      Scheme.fromSpecStalk_closedPoint

end GlobalTheory.GenTrait
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeDVR_point_genericPoint : ∀ (Z : Scheme.{0}) [IsIntegral Z] (W : Type) [CommRing W] [IsDomain W] [CharZero W] (_ : Sp W ⟶ Z), ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R), GlobalTheory.LN.CDvr R ∧ ∃ χ : Sp R ⟶ Z, ∀ y, χ y = genericPoint Z := by
  atlas_forward_decl GlobalTheory.GenTrait.exists_trait_genericPoint
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.TripleGlueMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem nonempty_cast {A B : Scheme.{0}} {t : SAB H A} {t' : SAB H B} {f g : A ⟶ B} (h : f = g)
    (m : SABMap t t' f) : Nonempty (SABMap t t' g) := by
  subst h
  exact ⟨m⟩

theorem exists_transport {A B : Scheme.{0}} (e : A ≅ B) (t : SAB H A) :
    ∃ t' : SAB H B, Nonempty (SABMap t' t e.inv) ∧ Nonempty (SABMap t t' e.hom) := by
  have hp := sabPull Out.CubePf.cubePull e.inv t
  have m := hp.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  obtain ⟨i, -⟩ := GlobalTheory.ObjMaps.exists_sab_id t
  obtain ⟨i'⟩ := nonempty_cast (by simp) i (g := e.hom ≫ e.inv)
  obtain ⟨k, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m i'
  exact ⟨_, ⟨m⟩, ⟨k⟩⟩

theorem mem_genericPoints_iso {A B : Scheme.{0}} (e : A ≅ B) (x : A) (hx : e.hom x ∈ genericPoints B) :
    x ∈ genericPoints A := by
  have hx' : closure {Scheme.homeoOfIso e x} ∈ irreducibleComponents B := by
    rw [Scheme.coe_homeoOfIso]
    exact hx
  have key := preimage_mem_irreducibleComponents hx' (Scheme.homeoOfIso e).isOpenEmbedding
    ⟨Scheme.homeoOfIso e x, subset_closure rfl, x, rfl⟩
  rw [(Scheme.homeoOfIso e).preimage_closure, ← Set.image_singleton,
    (Scheme.homeoOfIso e).injective.preimage_image] at key
  exact key

theorem generic_transport {A B : Scheme.{0}} (e : A ≅ B) {t : SAB H A} {t' : SAB H B} (m : SABMap t' t e.inv)
    (h : IsReduced A ∧ genericPoints A ⊆ abLocus t.G) : IsReduced B ∧ genericPoints B ⊆ abLocus t'.G := by
  obtain ⟨hr, hg⟩ := h
  refine ⟨@isReduced_of_isOpenImmersion _ _ e.inv _ hr, ?_⟩
  intro y hy
  have hy' : e.inv y ∈ genericPoints A := by
    apply mem_genericPoints_iso e
    have hyy : e.hom (e.inv y) = y := (Scheme.homeoOfIso e).apply_symm_apply y
    rw [hyy]
    exact hy
  have ha := hg hy'
  simp only [abLocus, Set.mem_setOf_eq] at ha ⊢
  intro K _ _ u hu
  have hp : IsProper (pullback.snd t.G.hom (u ≫ e.inv)) := by
    apply ha K (u ≫ e.inv)
    obtain ⟨p, rfl⟩ := hu
    exact ⟨p, rfl⟩
  have sq := (IsPullback.of_hasPullback t'.G.hom u).paste_horiz m.cart.1
  rw [← sq.isoIsPullback_hom_snd _ _ (IsPullback.of_hasPullback t.G.hom (u ≫ e.inv))]
  exact (MorphismProperty.cancel_left_of_respectsIso @IsProper _ _).mpr hp

theorem exists_sab_glue_of_isPullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  intro E _ _ _ H X X₀ X₁ X₂ ψ₁ ψ₂ φ₁ φ₂ t₀ t₁ t₂ m₁ m₂ h₁ h₂ sq hcov g₁ g₂
  obtain ⟨t₁', ⟨a₁⟩, ⟨b₁⟩⟩ := exists_transport ψ₁.isoOpensRange t₁
  obtain ⟨t₂', ⟨a₂⟩, ⟨b₂⟩⟩ := exists_transport ψ₂.isoOpensRange t₂
  have G₁ := generic_transport ψ₁.isoOpensRange a₁ g₁
  have G₂ := generic_transport ψ₂.isoOpensRange a₂ g₂
  have hr : Set.range (pullback.fst ψ₁ ψ₂ ≫ ψ₁) = Set.range (ψ₁.opensRange ⊓ ψ₂.opensRange).ι := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι]
    simp
  let e₀ : X₀ ≅ (ψ₁.opensRange ⊓ ψ₂.opensRange).toScheme :=
    sq.isoPullback ≪≫ IsOpenImmersion.isoOfRangeEq _ _ hr
  have he₀ : e₀.hom ≫ (ψ₁.opensRange ⊓ ψ₂.opensRange).ι = φ₁ ≫ ψ₁ := by
    simp [e₀]
  obtain ⟨t₀', ⟨a₀⟩, -⟩ := exists_transport e₀ t₀
  obtain ⟨c₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₁ a₀
  obtain ⟨d₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₁ c₁
  obtain ⟨c₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m₂ a₀
  obtain ⟨d₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp b₂ c₂
  have k₁ : (e₀.inv ≫ φ₁) ≫ ψ₁.isoOpensRange.hom =
      X.homOfLE (inf_le_left : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₁.opensRange) := by
    rw [← cancel_mono ψ₁.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← he₀, Iso.inv_hom_id_assoc]
  have k₂ : (e₀.inv ≫ φ₂) ≫ ψ₂.isoOpensRange.hom =
      X.homOfLE (inf_le_right : ψ₁.opensRange ⊓ ψ₂.opensRange ≤ ψ₂.opensRange) := by
    rw [← cancel_mono ψ₂.opensRange.ι]
    simp only [Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.homOfLE_ι]
    rw [← sq.w, ← he₀, Iso.inv_hom_id_assoc]
  obtain ⟨M₁⟩ := nonempty_cast k₁ d₁
  obtain ⟨M₂⟩ := nonempty_cast k₂ d₂
  have hUV : ψ₁.opensRange ⊔ ψ₂.opensRange = ⊤ := by
    ext x
    simp only [TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_top, Set.mem_union,
      Scheme.Hom.coe_opensRange, Set.mem_univ, iff_true]
    exact hcov x
  obtain ⟨t, n₁, n₂, -⟩ := GlobalTheory.TripleGlue.exists_sab_glue E H X _ _ t₁' t₂' t₀' M₁ M₂ hUV G₁ G₂
  obtain ⟨p₁, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₁ b₁
  obtain ⟨p₂, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ b₂
  exact ⟨t, nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₁) p₁,
    nonempty_cast (Scheme.Hom.isoOpensRange_hom_ι ψ₂) p₂⟩

end GlobalTheory.TripleGlueMap
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X₀ X₁ X₂ : Scheme.{0}) (ψ₁ : X₁ ⟶ X) (ψ₂ : X₂ ⟶ X) (φ₁ : X₀ ⟶ X₁) (φ₂ : X₀ ⟶ X₂) (t₀ : SAB H X₀) (t₁ : SAB H X₁) (t₂ : SAB H X₂) (_ : SABMap t₀ t₁ φ₁) (_ : SABMap t₀ t₂ φ₂), IsOpenImmersion ψ₁ → IsOpenImmersion ψ₂ → IsPullback φ₁ φ₂ ψ₁ ψ₂ → (∀ x : X, x ∈ Set.range ψ₁ ∨ x ∈ Set.range ψ₂) → (IsReduced X₁ ∧ genericPoints X₁ ⊆ abLocus t₁.G) → (IsReduced X₂ ∧ genericPoints X₂ ⊆ abLocus t₂.G) → ∃ t : SAB H X, Nonempty (SABMap t₁ t ψ₁) ∧ Nonempty (SABMap t₂ t ψ₂) := by
  first | exact @GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | exact GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback | (intros; apply GlobalTheory.TripleGlueMap.exists_sab_glue_of_isPullback <;> assumption)
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

noncomputable section

namespace GlobalTheory.ModelSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem range_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    Set.range (coprod.desc f g) = Set.range f ∪ Set.range g := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective x
    · exact .inl ⟨x, by rw [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact .inr ⟨x, by rw [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_desc]⟩
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(coprod.inl : X ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inl_desc]⟩
    · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) x, by rw [← Scheme.Hom.comp_apply, coprod.inr_desc]⟩

theorem isOpenImmersion_desc {X Y Z : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g]
    (h : Disjoint (Set.range f) (Set.range g)) : IsOpenImmersion (coprod.desc f g) := by
  let α : ∀ i : ULift.{0} WalkingPair, (i.1.casesOn X Y : Scheme.{0}) ⟶ Z := fun i => match i with
    | ⟨.left⟩ => f
    | ⟨.right⟩ => g
  have : ∀ i, IsOpenImmersion (α i) := by rintro ⟨_ | _⟩ <;> assumption
  have h₁ : IsOpenImmersion (Sigma.desc α) := isOpenImmersion_sigmaDesc _ α (by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ hij
    exacts [(hij rfl).elim, h, h.symm, (hij rfl).elim])
  have e : (coprodIsoSigma X Y).inv ≫ coprod.desc f g = Sigma.desc α := by
    refine Sigma.hom_ext _ _ ?_
    rintro ⟨_ | _⟩
    · rw [← Category.assoc, ι_left_coprodIsoSigma_inv, coprod.inl_desc, Sigma.ι_desc]
    · rw [← Category.assoc, ι_right_coprodIsoSigma_inv, coprod.inr_desc, Sigma.ι_desc]
  rw [(Iso.inv_comp_eq _).1 e]
  infer_instance

theorem isOpenImmersion_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (coprod.map f g) := by
  have e : coprod.map f g = coprod.desc (f ≫ coprod.inl) (g ≫ coprod.inr) := by ext <;> simp
  rw [e]
  refine isOpenImmersion_desc _ _ (Set.disjoint_left.2 ?_)
  rintro _ ⟨x, rfl⟩ ⟨y, hy⟩
  exact inr_ne_inl _ _ (f x) (g y) hy

theorem isDominant_map {X Y X' Y' : Scheme.{0}} (f : X ⟶ X') (g : Y ⟶ Y') [IsDominant f] [IsDominant g] :
    IsDominant (coprod.map f g) := by
  refine ⟨fun z => ?_⟩
  obtain ⟨x | x, rfl⟩ := (coprodMk _ _).surjective z
  · rw [coprodMk_inl]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inl : X' ⟶ X' ⨿ Y').continuous
      ⟨x, f.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inl : X ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inl_map, Scheme.Hom.comp_apply]⟩
  · rw [coprodMk_inr]
    refine closure_mono ?_ (image_closure_subset_closure_image (coprod.inr : Y' ⟶ X' ⨿ Y').continuous
      ⟨x, g.denseRange x, rfl⟩)
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨(coprod.inr : Y ⟶ X ⨿ Y) y, by rw [← Scheme.Hom.comp_apply, coprod.inr_map, Scheme.Hom.comp_apply]⟩

theorem mem_inl_or_inr {X Y : Scheme.{0}} (z : (X ⨿ Y : Scheme.{0})) :
    z ∈ Set.range (coprod.inl : X ⟶ X ⨿ Y) ∨ z ∈ Set.range (coprod.inr : Y ⟶ X ⨿ Y) :=
  (isCompl_range_inl_inr X Y).sup_eq_top.ge (Set.mem_univ z)

theorem isNormalScheme_coprod {X Y : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (hY : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Y) :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (X ⨿ Y) := by
  have key : ∀ {A : Scheme.{0}} (f : A ⟶ X ⨿ Y) [IsOpenImmersion f], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme A → ∀ a,
      IsDomain ((X ⨿ Y).presheaf.stalk (f a)) ∧ IsIntegrallyClosed ((X ⨿ Y).presheaf.stalk (f a)) := by
    intro A f _ hA a
    obtain ⟨h₁, h₂⟩ := hA a
    let e := (asIso (f.stalkMap a)).commRingCatIsoToRingEquiv
    exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩
  intro z
  obtain ⟨x, rfl⟩ | ⟨x, rfl⟩ := mem_inl_or_inr z
  exacts [key _ hX x, key _ hY x]

theorem isReduced_of_isNormalScheme {X : Scheme.{0}} (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) : IsReduced X :=
  have := fun x => (hX x).1
  isReduced_of_isReduced_stalk X

theorem noetherianSpace_of_isProjOver {O : Type} [CommRing O] [IsNoetherianRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp O}
    (h : IsProjOver s) : TopologicalSpace.NoetherianSpace Z := by
  obtain ⟨N, i, hi, rfl⟩ := h
  have : IsProper (PSpace.str O N) := isProper_str O N
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str O N)
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace (i ≫ PSpace.str O N)
  have : IsNoetherian Z := {}
  infer_instance

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

section
variable {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''}

theorem map_comp {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (m' : SABMap t'' t' g) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t k) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_comp m m').choose⟩

theorem map_cancel {f : S' ⟶ S} {g : S'' ⟶ S'} {k : S'' ⟶ S} (n : SABMap t'' t k) (m : SABMap t' t f)
    (h : g ≫ f = k) : Nonempty (SABMap t'' t' g) := by
  subst h
  exact ⟨(ObjMaps.exists_sab_cancel m n).choose⟩

theorem proper_of_map {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t.G.hom) : IsProper t'.G.hom :=
  MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 h

theorem lbIso_of_map {f : S' ⟶ S} (m : SABMap t' t f) : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
  obtain ⟨w, g, -⟩ := m.lin
  exact ⟨w, g⟩

theorem range_subset_abLocus {f : S' ⟶ S} (m : SABMap t' t f) (h : IsProper t'.G.hom) : Set.range f ⊆ abLocus t.G := by
  rintro _ ⟨x, rfl⟩
  exact (abLocus_pullback abLocusOne t.semi m.cart.1 x).2 fun _ _ _ _ _ => inferInstance

theorem genericPoints_subset_abLocus {f : S' ⟶ S} [IsDominant f] [TopologicalSpace.NoetherianSpace S']
    (m : SABMap t' t f) (h : IsProper t'.G.hom) : genericPoints S ⊆ abLocus t.G :=
  (genericPoints_subset_range_of_isDominant f).trans (range_subset_abLocus m h)

end

def HasModel {O : Type} [CommRing O] {M : Scheme.{0}} (sM : M ⟶ Sp O) (tM : SAB H M) (m n : ℕ) (r s : ℤ) : Prop :=
  ∃ C : ZOn sM tM m, C.amp.n = n ∧ C.amp.r = r ∧ C.amp.s = s

variable {O : Type} [CommRing O] {M : Scheme.{0}} {sM : M ⟶ Sp O} {tM : SAB H M} {m n : ℕ} {r s : ℤ}

theorem hasModel_of_maps {Y Z : Scheme.{0}} (a : Y ⟶ M) [IsOpenImmersion a] [IsDominant a] (j : Y ⟶ Z)
    [IsOpenImmersion j] [IsDominant j] (z : Z ⟶ Sp O) (h₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (h₂ : IsProjOver z) (h₃ : Flat z)
    (t : SAB H Z) (h₄ : IsQProjOver (t.G.hom ≫ z)) (h₅ : Models.Good t) (h : j ≫ z = a ≫ sM) {tY : SAB H Y}
    (m₁ : SABMap tY tM a) (m₂ : SABMap tY t j) (A : LN.AmpFrames t.G t.PP.L (m ^ 2)) :
    HasModel sM tM m A.n A.r A.s := by
  obtain ⟨tW, ⟨k⟩⟩ := exists_pull a.isoOpensRange.inv tY
  obtain ⟨k₁⟩ := map_comp k m₁ a.isoOpensRange_inv_comp
  obtain ⟨k₂⟩ := map_comp k m₂ rfl
  exact ⟨⟨Z, z, h₁, h₂, h₃, t, h₄, h₅, a.opensRange, a.denseRange, a.isoOpensRange.inv ≫ j, inferInstance, inferInstance,
    by rw [Category.assoc, h, ← Category.assoc, a.isoOpensRange_inv_comp], tW, k₁, k₂, A⟩, rfl, rfl, rfl⟩

theorem isDominant_ι {X : Scheme.{0}} {W : X.Opens} (h : Dense (W : Set X)) : IsDominant W.ι :=
  ⟨by rwa [DenseRange, Scheme.Opens.range_ι]⟩

theorem HasModel.shrink (h : HasModel sM tM m n r s) {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) : HasModel (i ≫ sM) tV m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  have : IsDominant (pullback.fst i C.W.ι) := isDominant_pullback_fst_of_isOpenMap _ _ i.isOpenEmbedding.isOpenMap
  have : IsDominant (pullback.snd i C.W.ι) := by
    have := isDominant_pullback_fst_of_isOpenMap i C.W.ι C.W.ι.isOpenEmbedding.isOpenMap
    rw [← pullbackSymmetry_hom_comp_fst]; infer_instance
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull (pullback.snd i C.W.ι) C.tW
  obtain ⟨p₁⟩ := map_comp p C.m₁ rfl
  obtain ⟨p₂⟩ := map_cancel p₁ k pullback.condition
  obtain ⟨p₃⟩ := map_comp p C.m₂ rfl
  exact hasModel_of_maps (pullback.fst i C.W.ι) (pullback.snd i C.W.ι ≫ C.j) C.s C.normal C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over, pullback.condition_assoc]) p₂ p₃ C.amp

theorem HasModel.grow {V : Scheme.{0}} (i : V ⟶ M) [IsOpenImmersion i] [IsDominant i]
    {tV : SAB H V} (k : SABMap tV tM i) (h : HasModel (i ≫ sM) tV m n r s) : HasModel sM tM m n r s := by
  obtain ⟨C, rfl, rfl, rfl⟩ := h
  have := isDominant_ι C.dense
  have := C.j_open
  have := C.j_dom
  obtain ⟨p⟩ := map_comp C.m₁ k rfl
  exact hasModel_of_maps (C.W.ι ≫ i) C.j C.s C.normal C.proj C.flat C.t C.qproj C.good
    (by rw [Category.assoc, C.j_over]) p C.m₂ C.amp

theorem hasModel_of_isEmpty [IsEmpty M] : HasModel sM tM m n r s := by
  have hp : ∀ {X : Scheme.{0}} [IsEmpty X] (f : X ⟶ Sp O), IsProjOver f := fun {X} _ f =>
    ProjSpace.isProjOver_of_disjoint_cover f (fun i : Empty => i.elim) (Subsingleton.elim _ _)
      (fun i => i.elim) fun i => i.elim
  have : IsEmpty tM.G.left := ⟨fun x => isEmptyElim (tM.G.hom x)⟩
  obtain ⟨k, -⟩ := ObjMaps.exists_sab_id tM
  obtain ⟨A, -, rfl, rfl, rfl⟩ := exists_ampFrames (G := tM.G) (L := tM.PP.L) (N := m ^ 2)
    (A := ⟨PEmpty, fun i => i.elim, fun i => i.elim⟩) (n := n) (r := r) (s := s)
    ⟨Subsingleton.elim _ _, fun i => i.elim, fun i => i.elim⟩ (fun z => isEmptyElim z)
    ⟨fun i => i.elim, fun i => i.elim, fun i => i.elim, fun i => i.elim⟩
  refine hasModel_of_maps (𝟙 M) (𝟙 M) sM (fun x => isEmptyElim x) (hp _) inferInstance tM ?_
    ⟨⟨⊤, Subsingleton.elim _ _, ?_⟩, fun x => isEmptyElim x, fun x => isEmptyElim x⟩ rfl k k A
  · obtain ⟨N, i, hi, e⟩ := hp (tM.G.hom ≫ sM)
    exact ⟨N, i, inferInstance, inferInstance, e⟩
  · have : IsEmpty (⊤ : M.Opens).toScheme := ⟨fun x => isEmptyElim x.1⟩
    infer_instance

theorem good_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : ∀ z, z ∈ Set.range f₁ ∨ z ∈ Set.range f₂) (g₁ : Models.Good t₁) (g₂ : Models.Good t₂) : Models.Good t := by
  let Y : Bool → Scheme.{0} := fun b => match b with | true => Z₁ | false => Z₂
  let f : ∀ b, Y b ⟶ Z := fun b => match b with | true => f₁ | false => f₂
  let u : ∀ b, SAB H (Y b) := fun b => match b with | true => t₁ | false => t₂
  let k : ∀ b, SABMap (u b) t (f b) := fun b => match b with | true => n₁ | false => n₂
  have ho : ∀ b, IsOpenImmersion (f b) := by rintro (_ | _) <;> assumption
  have hc : ∀ z, ∃ b, z ∈ Set.range (f b) := fun z => (h z).elim (fun h => ⟨true, h⟩) fun h => ⟨false, h⟩
  have hg : ∀ b, Models.Good (u b) := by rintro (_ | _) <;> assumption
  exact ⟨GlobalTheory.T.abelianLocus_isOpen_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).1, GlobalTheory.T.fibresSplit_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.1,
    GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover E H Z t _ Y f u k ho hc fun b => (hg b).2.2⟩

theorem qproj_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) (z : Z ⟶ Sp O) (g₁ : IsQProjOver (t₁.G.hom ≫ f₁ ≫ z))
    (g₂ : IsQProjOver (t₂.G.hom ≫ f₂ ≫ z)) : IsQProjOver (t.G.hom ≫ z) := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} {u : SAB H Y} (k : SABMap u t f),
      Set.range k.φ = t.G.hom ⁻¹' Set.range f := fun {Y f u} k => by
    rw [← Scheme.Pullback.range_fst, SABMap.φ, ← k.cart.1.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp,
      Set.range_comp, k.cart.1.isoPullback.hom.surjective.range_eq, Set.image_univ]
  refine GlobalTheory.T.isQProjOver_of_isCompl_openImmersions O _ _ _ n₁.φ n₂.φ _ (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₁.cart.1.flip ‹_›)
    (MorphismProperty.of_isPullback (P := @IsOpenImmersion) n₂.cart.1.flip ‹_›) ?_ ?_ ?_
  · rw [key, key]
    exact h.map (CompleteLatticeHom.setPreimage t.G.hom)
  · rwa [← Category.assoc, n₁.cart.1.w, Category.assoc]
  · rwa [← Category.assoc, n₂.cart.1.w, Category.assoc]

theorem amp_of_two {Z Z₁ Z₂ : Scheme.{0}} {f₁ : Z₁ ⟶ Z} {f₂ : Z₂ ⟶ Z} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {t : SAB H Z} {t₁ : SAB H Z₁} {t₂ : SAB H Z₂} (n₁ : SABMap t₁ t f₁) (n₂ : SABMap t₂ t f₂)
    (h : IsCompl (Set.range f₁) (Set.range f₂)) {N : ℕ} (A₁ : LN.AmpFrames t₁.G t₁.PP.L N)
    (A₂ : LN.AmpFrames t₂.G t₂.PP.L N) (hn : A₂.n = A₁.n) (hr : A₂.r = A₁.r) (hs : A₂.s = A₁.s) :
    ∃ A : LN.AmpFrames t.G t.PP.L N, A.n = A₁.n ∧ A.r = A₁.r ∧ A.s = A₁.s := by
  have key : ∀ {Y : Scheme.{0}} {f : Y ⟶ Z} [IsOpenImmersion f] {u : SAB H Y} (k : SABMap u t f)
      (A : LN.AmpFrames u.G u.PP.L N), HasFrames t.G t.PP.L N (pushLB f A.A) A.n A.r A.s := fun {Y f _ u} k A =>
    GlobalTheory.T.transitionFrames_push_openImmersion_image _ _ _ _ f k.φ _ _ t.PP.isLB u.PP.isLB k.cart.1 (lbIso_of_map k)
      (fun x hx => (abLocus_pullback abLocusOne t.semi k.cart.1 x).1 hx) N _ _ _ _ (hasFrames_of_ampFrames A)
  have h₂ := key n₂ A₂
  rw [hn, hr, hs] at h₂
  obtain ⟨a, b⟩ := GlobalTheory.T.isAmpleCechLineBundle_disjointUnion_pushforward Z Z₁ Z₂ f₁ f₂ A₁.A A₂.A h A₁.isLB A₂.isLB A₁.ample A₂.ample
  obtain ⟨A, -, e⟩ := exists_ampFrames a b (GlobalTheory.T.hasFrames_disjointUnionCechData Z _ _ N _ _ _ _ _ (fun i j => le_bot_iff.1 (by
    rintro _ ⟨⟨x, -, rfl⟩, y, -, e⟩
    exact (Set.disjoint_left.1 h.disjoint ⟨x, rfl⟩ ⟨y, e⟩).elim)) (key n₁ A₁) h₂)
  exact ⟨A, e⟩

theorem HasModel.sum [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {V₁ V₂ : Scheme.{0}} (i₁ : V₁ ⟶ M)
    (i₂ : V₂ ⟶ M) [IsOpenImmersion i₁] [IsOpenImmersion i₂] (hd : Disjoint (Set.range i₁) (Set.range i₂))
    (hu : Dense (Set.range i₁ ∪ Set.range i₂)) {t₁ : SAB H V₁} {t₂ : SAB H V₂} (k₁ : SABMap t₁ tM i₁)
    (k₂ : SABMap t₂ tM i₂) (h₁ : HasModel (i₁ ≫ sM) t₁ m n r s) (h₂ : HasModel (i₂ ≫ sM) t₂ m n r s) :
    HasModel sM tM m n r s := by
  obtain ⟨C₁, rfl, rfl, rfl⟩ := h₁
  obtain ⟨C₂, hn, hr, hs⟩ := h₂
  have := isDominant_ι C₁.dense
  have := C₁.j_open
  have := C₁.j_dom
  have := isDominant_ι C₂.dense
  have := C₂.j_open
  have := C₂.j_dom
  have := C₁.flat
  have := C₂.flat
  have o₀ := isOpenImmersion_desc i₁ i₂ hd
  have d₀ : IsDominant (coprod.desc i₁ i₂) := ⟨by rwa [DenseRange, range_desc]⟩
  have o₁ := isOpenImmersion_map C₁.W.ι C₂.W.ι
  have d₁ := isDominant_map C₁.W.ι C₂.W.ι
  let a := coprod.map C₁.W.ι C₂.W.ι ≫ coprod.desc i₁ i₂
  have o₂ := isOpenImmersion_map C₁.j (𝟙 C₂.W.toScheme)
  have d₂ := isDominant_map C₁.j (𝟙 C₂.W.toScheme)
  have o₃ := isOpenImmersion_map (𝟙 C₁.Z) C₂.j
  have d₃ := isDominant_map (𝟙 C₁.Z) C₂.j
  have hZ := isNormalScheme_coprod C₁.normal C₂.normal
  have hP := ProjSpace.isProjOver_coprodDesc C₁.proj C₂.proj
  have := noetherianSpace_of_isProjOver hP
  have := isReduced_of_isNormalScheme hZ
  have : TopologicalSpace.NoetherianSpace (C₁.W.toScheme ⨿ C₂.W.toScheme : Scheme.{0}) :=
    (coprod.map C₁.j (𝟙 C₂.W.toScheme) ≫ coprod.map (𝟙 C₁.Z) C₂.j).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₁.W.toScheme :=
    (coprod.inl : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  have : TopologicalSpace.NoetherianSpace C₂.W.toScheme :=
    (coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme).isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨tY, ⟨p⟩⟩ := exists_pull a tM
  obtain ⟨q₁⟩ := map_comp C₁.m₁ k₁ rfl
  obtain ⟨q₂⟩ := map_comp C₂.m₁ k₂ rfl
  obtain ⟨p₁⟩ := map_cancel (g := coprod.inl) q₁ p (by rw [coprod.inl_map_assoc, coprod.inl_desc])
  obtain ⟨p₂⟩ := map_cancel (g := coprod.inr) q₂ p (by rw [coprod.inr_map_assoc, coprod.inr_desc])
  have pY := proper_of_map p hp
  obtain ⟨t', ⟨u₀⟩, ⟨u₁⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map C₁.j (𝟙 C₂.W.toScheme)) coprod.inl coprod.inl C₁.j _ _ _
    p₁ C₁.m₂ o₂ inferInstance (isPullback_inl_inl_coprodMap _ _).flip (fun x => by
      obtain h | ⟨y, rfl⟩ := mem_inl_or_inr x
      · exact .inr h
      · exact .inl ⟨(coprod.inr : _ ⟶ C₁.W.toScheme ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inr_map, Category.id_comp]⟩)
    ⟨isReduced_of_isOpenImmersion a, fun _ _ _ _ _ _ _ => inferInstance⟩
    ⟨isReduced_of_isNormalScheme C₁.normal, genericPoints_subset_abLocus C₁.m₂ (proper_of_map q₁ hp)⟩
  obtain ⟨v₂⟩ := map_comp (k := coprod.inr) p₂ u₀ (by simp)
  obtain ⟨t, ⟨w₀⟩, ⟨w₂⟩⟩ := GlobalTheory.T.exists_abelianTriple_glue_two_open_immersions E H _ _ _ _ (coprod.map (𝟙 C₁.Z) C₂.j) coprod.inr coprod.inr C₂.j _ _ _
    v₂ C₂.m₂ o₃ inferInstance (isPullback_inr_inr_coprodMap _ _).flip (fun x => by
      obtain ⟨y, rfl⟩ | h := mem_inl_or_inr x
      · exact .inl ⟨(coprod.inl : _ ⟶ C₁.Z ⨿ C₂.W.toScheme) y, by
          rw [← Scheme.Hom.comp_apply, coprod.inl_map, Category.id_comp]⟩
      · exact .inr h)
    ⟨isReduced_of_isOpenImmersion (coprod.map (𝟙 C₁.Z) C₂.j), genericPoints_subset_abLocus u₀ pY⟩
    ⟨isReduced_of_isNormalScheme C₂.normal, genericPoints_subset_abLocus C₂.m₂ (proper_of_map q₂ hp)⟩
  obtain ⟨w₁⟩ := map_comp (k := coprod.inl) u₁ w₀ (by simp)
  obtain ⟨w⟩ := map_comp u₀ w₀ rfl
  obtain ⟨A, e₁, e₂, e₃⟩ := amp_of_two w₁ w₂ (isCompl_range_inl_inr _ _) C₁.amp C₂.amp hn hr hs
  rw [← e₁, ← e₂, ← e₃]
  refine hasModel_of_maps a _ (coprod.desc C₁.s C₂.s) hZ hP ?_ t
    (qproj_of_two w₁ w₂ (isCompl_range_inl_inr _ _) _ (by rw [coprod.inl_desc]; exact C₁.qproj)
      (by rw [coprod.inr_desc]; exact C₂.qproj))
    (good_of_two w₁ w₂ mem_inl_or_inr C₁.good C₂.good) ?_ p w A
  · have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
    refine IsZariskiLocalAtSource.of_openCover (P := @Flat) (coprodOpenCover.{0, 0} C₁.Z C₂.Z) ?_
    rintro (_ | _)
    · exact (coprod.inl_desc C₁.s C₂.s).symm ▸ C₁.flat
    · exact (coprod.inr_desc C₁.s C₂.s).symm ▸ C₂.flat
  · refine coprod.hom_ext ?_ ?_
    · simp only [a, Category.assoc, coprod.inl_map_assoc, coprod.inl_desc, coprod.inl_desc_assoc, Category.id_comp,
        C₁.j_over]
    · simp only [a, Category.assoc, coprod.inr_map_assoc, coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp,
        C₂.j_over]

theorem hasModel_sup [IsNoetherianRing O] [IsReduced M] (hp : IsProper tM.G.hom) {I : Type} (V : I → M.Opens)
    (hd : ∀ i j, i ≠ j → Disjoint (V i) (V j))
    (h : ∀ i (t : SAB H (V i).toScheme), SABMap t tM (V i).ι → HasModel ((V i).ι ≫ sM) t m n r s) (S : Finset I) :
    ∀ t : SAB H (S.sup V).toScheme, SABMap t tM (S.sup V).ι → HasModel ((S.sup V).ι ≫ sM) t m n r s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro t _
    have : IsEmpty ((∅ : Finset I).sup V).toScheme := ⟨fun x => x.2⟩
    exact hasModel_of_isEmpty
  | insert a S ha ih =>
    intro t k
    have l₁ : V a ≤ (insert a S).sup V := Finset.le_sup (Finset.mem_insert_self a S)
    have l₂ : S.sup V ≤ (insert a S).sup V := Finset.sup_mono (Finset.subset_insert a S)
    have hD : Disjoint (V a) (S.sup V) := Finset.disjoint_sup_right.2 fun j hj => hd a j fun e => ha (e ▸ hj)
    obtain ⟨t₁, ⟨k₁⟩⟩ := exists_pull (M.homOfLE l₁) t
    obtain ⟨t₂, ⟨k₂⟩⟩ := exists_pull (M.homOfLE l₂) t
    obtain ⟨q₁⟩ := map_comp k₁ k (M.homOfLE_ι l₁)
    obtain ⟨q₂⟩ := map_comp k₂ k (M.homOfLE_ι l₂)
    refine HasModel.sum (proper_of_map k hp) (M.homOfLE l₁) (M.homOfLE l₂) (Set.disjoint_left.2 ?_) (fun x => ?_) k₁ k₂
      (by rw [Scheme.homOfLE_ι_assoc]; exact h a t₁ q₁) (by rw [Scheme.homOfLE_ι_assoc]; exact ih t₂ q₂)
    · rintro _ ⟨x, rfl⟩ ⟨y, e⟩
      have e' : y.1 = x.1 := (Scheme.homOfLE_apply l₂ y).symm.trans ((congrArg Subtype.val e).trans (Scheme.homOfLE_apply l₁ x))
      exact hD.le_bot (⟨x.2, e' ▸ y.2⟩ : x.1 ∈ V a ⊓ S.sup V)
    · refine subset_closure ?_
      obtain hx | hx : x.1 ∈ V a ∨ x.1 ∈ S.sup V := (Finset.sup_insert (s := S) (f := V) (b := a)).le x.2
      · exact .inl ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩
      · exact .inr ⟨⟨x.1, hx⟩, Subtype.ext (by simp)⟩

theorem rank_eq (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {R : Type} [CommRing R]
    [IsLocalRing R] {y : Sp R ⟶ M} {t' : SAB H (Sp R)} (k : SABMap t' tM y) {Z : Scheme.{0}} {t : SAB H Z}
    {χ : Sp R ⟶ Z} (k' : SABMap t' t χ) {N : ℕ} {T : Over Z} (h : Over.mk χ ⟶ T)
    (b : Fin n → LB.Sec (Out.LPow t.G t.PP.L (N : ℤ) T)) (hb : LN.BasisAlong t.G t.PP.L N h b) : n = max 1 (N ^ g) := by
  obtain ⟨b', hb'⟩ := GlobalTheory.T.pulledSectionsFormBasis_id_of_pulledSectionsFormBasis Z _ _ N n _ _ h b t.PP.isLB hb
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_sectionPower_transport_cartesian_square Z _ t.G t'.G χ k'.φ _ _ t.PP.isLB t'.PP.isLB k'.cart.1 (lbIso_of_map k') N
  let e₀ := e (Over.mk (𝟙 (Sp R))) (Over.mk χ) (Iso.refl _) rfl
  have hb₀ : LN.BasisAlong t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) := fun σ => by
    have key : ∀ c, LN.Lin t'.G t'.PP.L N (𝟙 (Over.mk (𝟙 (Sp R)))) (fun i => e₀.symm (b' i)) c σ ↔
        LN.Lin t.G t.PP.L N (𝟙 (Over.mk χ)) b' c (e₀ σ) := fun c => by
      have := he _ _ _ _ (Iso.refl _) (Iso.refl _) rfl rfl (𝟙 (Over.mk (𝟙 (Sp R)))) (𝟙 (Over.mk χ)) rfl n
        (fun i => e₀.symm (b' i)) c σ
      refine this.trans ?_
      rw [show (fun i => e _ _ (Iso.refl _) rfl (e₀.symm (b' i))) = b' from funext fun i => e₀.apply_symm_apply _]
    simp only [key]
    exact hb' _
  have := t'.semi.smooth
  have := t'.semi.geomConnected
  obtain ⟨w, gw, -⟩ := k.lin
  obtain ⟨U, hU, hc, -⟩ := exists_isAffineOpen_mem_and_subset (X := M) (U := ⊤)
    (x := y (IsLocalRing.closedPoint R)) trivial
  have hy : ∀ x, y x ∈ U := fun x =>
    (congrArg (fun V => x ∈ V) (Scheme.preimage_eq_top_of_closedPoint_mem y hc)).mpr trivial
  have am := relAmple_pull k.cart.1 tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) U hU hy hA
  have kt := kTriv_pull k.cart tM.PP.isLB t'.PP.isLB ((isGen_iff w).1 gw) hK
  obtain ⟨-, ws, gs', -⟩ := t'.sym
  let P : Out.PolAV (Sp R) :=
    { A := t'.G, g := g, L := t'.PP.L, isLB := t'.PP.isLB, ample := am, ktriv := kt
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback k.cart.1 hg
      isAb := ⟨inferInstance, inferInstance, proper_of_map k hp, ‹_›⟩
      rigid := ⟨t'.PP.rig, t'.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  obtain rfl | hN := Nat.eq_zero_or_pos N
  · rw [GlobalTheory.T.card_basis_polarisation_power_zero_eq_one hL.globalFns R P n _ hb₀, max_eq_left (pow_le_one₀ le_rfl zero_le_one)]
  · rw [GlobalTheory.T.card_pulledSectionsFormBasis_eq_pow_dim hL hL' R P N n _ hN hb₀, max_eq_right (Nat.one_le_pow _ _ hN)]

theorem hasModel_rank (hL : Out.Laws) (hL' : Out.Laws2) (hp : IsProper tM.G.hom) (hA : Out.RelAmple tM.G tM.PP.L)
    (hK : Out.KTriv tM.G tM.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g tM.G.hom) {V : Scheme.{0}} {i : V ⟶ M}
    {tV : SAB H V} (k : SABMap tV tM i) {sV : V ⟶ Sp O} (C : ZOn sV tV m) [IsIntegral C.Z]
    (A : LN.AmpFrames C.t.G C.t.PP.L (m ^ 2)) : HasModel sV tV m (max 1 ((m ^ 2) ^ g)) A.r A.s := by
  suffices h : HasFrames C.t.G C.t.PP.L (m ^ 2) A.A (max 1 ((m ^ 2) ^ g)) A.r A.s by
    obtain ⟨A', -, e⟩ := exists_ampFrames A.isLB A.ample h
    exact ⟨{ C with amp := A' }, e⟩
  by_cases hT : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], LN.CDvr W → IsEmpty (Sp W ⟶ C.Z)
  · exact GlobalTheory.T.hasTransitionCompatibleFrames_of_no_completeDVR_points _ _ _ _ _ _ _ _ _ (le_max_left _ _) hT (hasFrames_of_ampFrames A)
  push Not at hT
  obtain ⟨W, _, _, _, hW, ⟨χ₀⟩⟩ := hT
  have := hW.2.2
  obtain ⟨R, _, _, _, hR, χ, hχ⟩ := GlobalTheory.T.exists_completeDVR_point_genericPoint C.Z W χ₀
  have := C.j_open
  have := C.j_dom
  have hj : Set.range χ ⊆ Set.range C.j := by
    rintro _ ⟨y, rfl⟩
    rw [hχ]
    exact ((genericPoint_spec C.Z).mem_open_set_iff C.j.isOpenEmbedding.isOpen_range).2
      (by rw [Set.univ_inter]; exact C.j.denseRange.nonempty_iff.2 inferInstance |>.elim fun x => ⟨_, x, rfl⟩)
  obtain ⟨a, ha⟩ := exists_chart A.isLB (genericPoint C.Z)
  have hU : Set.range χ ⊆ Set.range (A.A.U a).ι := by
    rintro _ ⟨y, rfl⟩
    rw [hχ, Scheme.Opens.range_ι]
    exact ha
  obtain ⟨t', ⟨p⟩⟩ := exists_pull (IsOpenImmersion.lift C.j χ hj) C.tW
  obtain ⟨q⟩ := map_comp C.m₁ k rfl
  obtain ⟨p₁⟩ := map_comp p q rfl
  obtain ⟨p₂⟩ := map_comp (k := IsOpenImmersion.lift (A.A.U a).ι χ hU ≫ (A.A.U a).ι) p C.m₂
    (by rw [IsOpenImmersion.lift_fac, IsOpenImmersion.lift_fac])
  have hb := (A.trait a R hR (IsOpenImmersion.lift (A.A.U a).ι χ hU) (by
    rintro _ ⟨y, rfl⟩
    exact range_subset_abLocus p₂ (proper_of_map p₁ hp) ⟨_, rfl⟩)).2
  rw [← rank_eq hL hL' hp hA hK hg p₁ p₂ _ _ hb]
  exact hasFrames_of_ampFrames A

end GlobalTheory.ModelSum

namespace GlobalTheory

open ModelSum ZM in

theorem Models.nonempty_zOn_of_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (O : Type) [CommRing O] [IsNoetherianRing O] (MM : Scheme.{0}) (sM : MM ⟶ Sp O) (tM : SAB H MM) (m : ℕ), IsReduced MM → LocallyOfFiniteType sM → QuasiCompact sM → (∀ ξ ∈ genericPoints MM, ∃ (V : Scheme.{0}) (i : V ⟶ MM) (tV : SAB H V) (_ : SABMap tV tM i) (C : ZOn (i ≫ sM) tV m), IsOpenImmersion i ∧ ξ ∈ Set.range i ∧ IsIntegral V ∧ IsIntegral C.Z ∧ C.amp.s = 1 ∧ ∀ r : ℤ, C.amp.r ≤ r → ∃ A : GlobalTheory.LN.AmpFrames C.t.G C.t.PP.L (m ^ 2), A.r = r ∧ A.s = 1) → (∃ g, SmoothOfRelativeDimension g tM.G.hom) → Out.Laws → Out.Laws2 → IsProper tM.G.hom → Out.RelAmple tM.G tM.PP.L → Out.KTriv tM.G tM.PP.L → Nonempty (ZOn sM tM m) := by
  intro E _ _ _ H O _ _ M sM tM m hr hf hq h ⟨g, hg⟩ hL hL' hp hA hK
  have : IsLocallyNoetherian M := LocallyOfFiniteType.isLocallyNoetherian sM
  have : CompactSpace M := QuasiCompact.compactSpace_of_compactSpace sM
  have : IsNoetherian M := {}
  have hfin : (genericPoints M).Finite := genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  have : Fintype (genericPoints M) := hfin.fintype
  choose V i tV k C ho hm hV hZ hs hC using fun ξ : genericPoints M => h ξ.1 ξ.2
  obtain ⟨r, hb⟩ := (Set.finite_range fun ξ => (C ξ).amp.r).bddAbove
  have gen : ∀ ξ x, ξ.1 ⤳ i ξ x := fun ξ x => by
    obtain ⟨v, hv⟩ := hm ξ
    have e : i ξ (genericPoint (V ξ)) = ξ.1 := eq_of_specializes_of_mem_genericPoints ξ.2
      (hv ▸ (genericPoint_specializes v).map (i ξ).continuous)
    exact e ▸ (genericPoint_specializes x).map (i ξ).continuous
  have key := hasModel_sup (sM := sM) (m := m) (n := max 1 ((m ^ 2) ^ g)) (r := r) (s := 1) hp
    (fun ξ => (i ξ).opensRange) (fun ξ ζ hne => disjoint_iff_inf_le.2 (by
      rintro _ ⟨⟨x, rfl⟩, hy⟩
      obtain ⟨c, hc⟩ := (gen ξ x).mem_open (i ζ).opensRange.2 hy
      exact (hne (Subtype.ext (eq_of_specializes_of_mem_genericPoints ξ.2 (hc ▸ gen ζ c)).symm)).elim))
    (fun ξ t q => by
      obtain ⟨A, rfl, e⟩ := hC ξ r (hb ⟨ξ, rfl⟩)
      obtain ⟨q'⟩ := map_cancel q (k ξ) (i ξ).isoOpensRange_inv_comp
      have := (hasModel_rank hL hL' hp hA hK hg (k ξ) (C ξ) A).shrink (i ξ).isoOpensRange.inv q'
      rwa [← Category.assoc, (i ξ).isoOpensRange_inv_comp, e] at this) Finset.univ
  obtain ⟨t, ⟨q⟩⟩ := exists_pull (Finset.univ.sup fun ξ => (i ξ).opensRange : M.Opens).ι tM
  have := isDominant_ι (W := Finset.univ.sup fun ξ => (i ξ).opensRange)
    ((dense_iff_closure_eq.2 (genericPoints.closure (α := M))).mono fun ξ hξ =>
      Finset.le_sup (f := fun ξ => (i ξ).opensRange) (Finset.mem_univ ⟨ξ, hξ⟩) (hm ⟨ξ, hξ⟩))
  exact ⟨(HasModel.grow _ q (key t q)).choose⟩

end GlobalTheory

end
end
