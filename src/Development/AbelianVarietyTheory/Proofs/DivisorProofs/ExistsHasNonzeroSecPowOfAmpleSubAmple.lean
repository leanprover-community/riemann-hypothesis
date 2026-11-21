import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPowVanishingIdealLeAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensOfForallIsPsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SheafCohomologyDimTwistCutInequalities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow

section
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.SiuChain

theorem hdim_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)]
    (hX : IsProjOver (strHom k X)) (G : X.Modules) [IsFiniteQC G] (B M : LB X) (hB : B.IsLB)
    (hM : M.IsLB) (t : B.Sec) (ht : Mono (cutHom G hB t)) (j : ℕ) :
    ∀ (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist G M') 0 ≤ hdim k (twist G M) 0 := by
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G hM hM' h
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h2 := ih _ (isLB_tens hM' hB) (by rw [h1, h, succ_nsmul']; abel)
    exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX G B _ M' hB _ hM' t ht h1).2.2).trans h2

theorem hdim_le_add_mul_hdim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  intro k _ _ X _ hX F _ B M hB hM s t hs ht j
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' h
    rw [hdim_congr k 0 e]
    omega
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h0 : cls M hM = cls (tens M' B) (isLB_tens hM' hB) + j • cls B hB := by
      rw [h1, h, succ_nsmul']; abel
    have h2 := ih _ (isLB_tens hM' hB) h0
    have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B _ M' hB _ hM' s hs h1).1 0
    have h4 := hdim_le_of_cls_eq_add_nsmul k X hX (cut F hB s) B M hB hM t ht j _
      (isLB_tens hM' hB) h0
    rw [Nat.succ_mul]
    omega

end GlobalTheory.SiuChain
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  atlas_forward_decl GlobalTheory.SiuChain.hdim_le_add_mul_hdim_cut
end

section
namespace GlobalTheory

theorem morse_inequality_arith (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ)
    (H1 : ∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤
      C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1)))
    (H2 : ∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤
      C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)))
    (hab : ((d : ℤ) + 1) * b < a) : ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = C * (d + 1) + (d + 1) * C' * d := ⟨_, rfl⟩
  obtain ⟨m, hm0, hm1, hmK⟩ : ∃ m : ℕ, m₀ ≤ m ∧ m₁ ≤ m ∧ K * 2 ^ d + 1 ≤ m :=
    ⟨m₀ + m₁ + (K * 2 ^ d + 1), by omega, by omega, by omega⟩
  have hm : 1 ≤ m := le_trans (Nat.le_add_left 1 _) hmK
  refine ⟨m, hm, ?_⟩
  by_contra hcon
  have hcon' : (h m : ℤ) ≤ (m : ℤ) * g m := by exact_mod_cast not_lt.mp hcon
  have h1 := (abs_le.mp (H1 m hm0)).1
  have h2 := (abs_le.mp (H2 m hm1)).2
  rw [Nat.add_sub_cancel, Nat.factorial_succ] at h1
  push_cast at h1
  have hM : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have hMK : (K : ℤ) * 2 ^ d + 1 ≤ m := by exact_mod_cast hmK
  have hKz : (K : ℤ) = C * ((d : ℤ) + 1) + (d + 1) * C' * d := by rw [hK]; push_cast; ring
  generalize (m : ℤ) = M at *
  have hF : (0 : ℤ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hd : (0 : ℤ) ≤ d := by positivity
  have hA : M * ((d : ℤ) * (M + 1) ^ (d - 1)) ≤ d * (M + 1) ^ d := by
    rcases d with _ | e
    · simp
    · rw [Nat.add_sub_cancel, pow_succ]
      have : (0 : ℤ) ≤ ((e + 1 : ℕ) : ℤ) * (M + 1) ^ e := by positivity
      nlinarith
  have hP : (M + 1) ^ d ≤ 2 ^ d * M ^ d := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) (by linarith) d
  have hQ : 0 < M ^ d := by positivity
  have e1 : ((d : ℤ) + 1) * d.factorial * h m ≤ ((d : ℤ) + 1) * d.factorial * (M * g m) :=
    mul_le_mul_of_nonneg_left hcon' (by positivity)
  have e2 : ((d : ℤ) + 1) * M * ((d.factorial : ℤ) * g m - b * M ^ d) ≤
      ((d : ℤ) + 1) * M * (C' * ((d : ℤ) * (M + 1) ^ (d - 1))) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have e3 : ((d : ℤ) + 1) * C' * (M * ((d : ℤ) * (M + 1) ^ (d - 1))) ≤
      ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) :=
    mul_le_mul_of_nonneg_left hA (by positivity)
  have e4 : (K : ℤ) * (M + 1) ^ d ≤ K * (2 ^ d * M ^ d) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have e5 : ((K : ℤ) * 2 ^ d + 1) * M ^ d ≤ M * M ^ d :=
    mul_le_mul_of_nonneg_right hMK hQ.le
  have e6 : (((d : ℤ) + 1) * b + 1) * (M * M ^ d) ≤ a * (M * M ^ d) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e7 : (K : ℤ) * (M + 1) ^ d =
      C * ((d + 1) * (M + 1) ^ d) + ((d : ℤ) + 1) * C' * (d * (M + 1) ^ d) := by
    rw [hKz]; ring
  rw [pow_succ' M d] at h1
  linarith

end GlobalTheory
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds : ∀ (d : ℕ) (a b : ℤ) (h g : ℕ → ℕ) (C C' m₀ m₁ : ℕ), (∀ m : ℕ, m₀ ≤ m → |((d + 1).factorial : ℤ) * (h m : ℤ) - a * (m : ℤ) ^ (d + 1)| ≤ C * (((d + 1 : ℕ) : ℤ) * ((m : ℤ) + 1) ^ (d + 1 - 1))) → (∀ m : ℕ, m₁ ≤ m → |(d.factorial : ℤ) * (g m : ℤ) - b * (m : ℤ) ^ d| ≤ C' * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1))) → ((d : ℤ) + 1) * b < a → ∃ m : ℕ, 1 ≤ m ∧ m * g m < h m := by
  atlas_forward_decl GlobalTheory.morse_inequality_arith
end

section
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_sec_of_ample_sub_generated :
    ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hp d hd L B M hL hB hM e hlt
  have hf := algebraMap_eq_strHom k X
  have := isNoetherian_of_isProjOver hp
  have hsd : suppDim (GlobalTheory.structureModule X) ≤ (d + 1 : ℕ) := by
    rw [suppDim_structureModule]; exact hd
  have hfin := finiteCohTwists_of_isProjOver hf (GlobalTheory.structureModule X) hp
  obtain ⟨s, hs⟩ := IsGenerated.exists_mono_cutHom k (GlobalTheory.structureModule X) hB
  set G := cut (GlobalTheory.structureModule X) hB.isLB s with hG
  haveI : IsFiniteQC G := isFiniteQC_cut (GlobalTheory.structureModule X) hB.isLB s
  obtain ⟨t, ht⟩ := IsGenerated.exists_mono_cutHom k G hB
  have hGd : suppDim G ≤ (d : ℕ) := suppDim_cut_le _ hB.isLB s hsd
  have hcut := interNum_cons_eq_interNum_cut hB.isLB s (P := fun _ : Fin d => L) (fun _ => hL.isLB) hfin
  obtain ⟨C, m₀, hC⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp (d + 1) (GlobalTheory.structureModule X) hsd L hL
  obtain ⟨C', m₁, hC'⟩ := GlobalTheory.T.asymptotic_riemannRoch_ample_coherent k X hp d G hGd L hL
  rw [hcut] at hlt
  obtain ⟨m, hm1, hm⟩ := GlobalTheory.T.exists_mul_lt_of_asymptotic_bounds d (topSelfIntersection k L (d + 1)) (interNum k G (fun _ : Fin d => L))
    (fun m => hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0)
    (fun m => hdim k (twist G (lbPow L m)) 0) C C' m₀ m₁ hC hC' hlt
  have hcl : cls (lbPow L m) (isLB_lbPow hL.isLB m) =
      cls (lbPow M m) (isLB_lbPow hM m) + m • cls B hB.isLB := by
    rw [cls_lbPow hL.isLB, cls_lbPow hM, e, smul_add]
  have hch := GlobalTheory.T.sectionsDim_le_add_mul_sectionsDim_cut k X hp (GlobalTheory.structureModule X) B (lbPow L m) hB.isLB (isLB_lbPow hL.isLB m)
    s t hs ht m (lbPow M m) (isLB_lbPow hM m) hcl
  have hch' : hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 ≤
      hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0 + m * hdim k (twist G (lbPow L m)) 0 := hch
  refine ⟨m, hm1, lineBundleHasNonzeroSection_of_globalSectionsDim_pos (k := k) ?_⟩
  show 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow M m)) 0
  have : m * hdim k (twist G (lbPow L m)) 0 < hdim k (twist (GlobalTheory.structureModule X) (lbPow L m)) 0 := hm
  omega

end GlobalTheory
end
end

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_morse_exists_section_ample_sub_generated : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsGenerated B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  atlas_forward_decl GlobalTheory.exists_sec_of_ample_sub_generated
end

section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem exists_hasNonzeroSec_pow_of_ample_sub_ample : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ d : ℕ, topologicalKrullDim X ≤ (d + 1 : ℕ) → ∀ (L B M : LB X) (hL : IsAmpleLB L) (hB : IsAmpleLB B) (hM : M.IsLB), cls L hL.isLB = cls M hM + cls B hB.isLB → ((d : ℤ) + 1) * interNum k (GlobalTheory.structureModule X) (Fin.cons B (fun _ : Fin d => L) : Fin (d + 1) → LB X) < topSelfIntersection k L (d + 1) → ∃ r, 1 ≤ r ∧ HasNonzeroSec (lbPow M r) := by
  intro k _ _ X _ _ hX d hdim L B M hL hB hM hcls hineq

  have hgen : ∀ᶠ n : ℕ in atTop, IsGenerated (lbPow B n) := by
    filter_upwards [hB.eventually_isGloballyGenerated_twist (LB.unitMod X)] with n hn
    obtain ⟨ι, hι, φ, hφ⟩ := hn
    exact (isGloballyGenerated_toMod_iff (isLB_lbPow hB.isLB n)).1
      ⟨ι, hι, φ ≫ (unitTwistIso (X := X) (L := lbPow B n)).hom, epi_comp _ _⟩
  obtain ⟨m, hmB, hm1⟩ := (hgen.and (eventually_ge_atTop 1)).exists

  have hLm : IsAmpleLB (lbPow L m) := (isAmpleLB_basic.2.1 hL.isLB hm1).2 hL
  have hMm : (lbPow M m).IsLB := isLB_lbPow hM m
  have hclsm : cls (lbPow L m) hLm.isLB = cls (lbPow M m) hMm + cls (lbPow B m) hmB.isLB := by
    rw [CechPic.cls_lbPow hL.isLB m, CechPic.cls_lbPow hM m, CechPic.cls_lbPow hB.isLB m, hcls,
      smul_add]

  have hv : DiffVanish (d + 1 + 1) (chiPic k (structureModule X)) := by
    apply diffVanish_chiPic_of_isProjOver (f := strHom k X) (algebraMap_eq_strHom k X) _ hX
    unfold QCoh.suppDim
    exact (topologicalKrullDim_subspace_le _ _).trans hdim
  have hprod : (∏ _i : Fin (d + 1), (m : ℤ)) = (m : ℤ) ^ (d + 1) := by simp
  have hP : ∀ i, ((Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hB.isLB
    · exact hL.isLB
  have hQ : ∀ i, ((Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) i).IsLB := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hmB.isLB
    · exact hLm.isLB
  have hI : interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) =
      (m : ℤ) ^ (d + 1) * interNum k (structureModule X)
        (Fin.cons B fun _ : Fin d => L : Fin (d + 1) → LB X) := by
    rw [← hprod]
    refine hv.interNum_of_cls_eq_zsmul hP hQ (fun _ => (m : ℤ)) ?_
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (CechPic.cls_lbPow hB.isLB m _).trans (natCast_zsmul _ _).symm
    · exact (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm
  have hT : topSelfIntersection k (lbPow L m) (d + 1) = (m : ℤ) ^ (d + 1) * topSelfIntersection k L (d + 1) := by
    rw [topSelf_def, topSelf_def, ← hprod]
    exact hv.interNum_of_cls_eq_zsmul (fun _ => hL.isLB) (fun _ => hLm.isLB) (fun _ => (m : ℤ))
      (fun _ => (CechPic.cls_lbPow hL.isLB m _).trans (natCast_zsmul _ _).symm)
  have hpos : (0 : ℤ) < (m : ℤ) ^ (d + 1) := pow_pos (by exact_mod_cast hm1) _
  have hineqm : ((d : ℤ) + 1) * interNum k (structureModule X)
      (Fin.cons (lbPow B m) fun _ : Fin d => lbPow L m : Fin (d + 1) → LB X) <
      topSelfIntersection k (lbPow L m) (d + 1) := by
    rw [hI, hT, mul_left_comm]
    exact mul_lt_mul_of_pos_left hineq hpos

  obtain ⟨r, hr, hs⟩ :=
    T.algebraic_morse_exists_section_ample_sub_generated k X hX d hdim (lbPow L m) (lbPow B m) (lbPow M m) hLm hmB hMm hclsm hineqm
  refine ⟨m * r, Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
  refine hs.of_cls_eq (isLB_lbPow hM (m * r)) (isLB_lbPow hMm r) ?_
  rw [CechPic.cls_lbPow hM (m * r), CechPic.cls_lbPow hMm r, CechPic.cls_lbPow hM m, smul_smul,
    mul_comm]

end GlobalTheory
end
