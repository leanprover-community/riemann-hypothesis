import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceConjStabilizesFramedLatticeIff
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsReductionOfMemLevelZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TruePackTwistPlacePropertyStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

theorem GlobalTheory.LocRed.red_entry_movedFrame : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  intro D k _ _ _ _ q PP hPP ϖ _ V β Λ N _ Y _ _ F σ b hb g gk hg hSt a a' z hz
  have hM : (mt V g).map q.pr * F.β.submatrix id σ = F.β.submatrix id σ * gk.val.submatrix σ σ := by
    have h1 : (mt V g).map q.pr = F.β * gk.val * F.γ := hg.2
    have hs : ∀ A : Matrix (Fin V.rank) (Fin V.rank) k, A * F.β.submatrix id σ = (A * F.β).submatrix id σ := fun A => by
      ext i j; simp [Matrix.mul_apply]
    rw [h1, Matrix.submatrix_mul_equiv F.β gk.val id σ σ, hs, Matrix.mul_assoc (F.β * gk.val), F.γβ, Matrix.mul_one]
  have key := GlobalTheory.SeeSaw.LevRed.red_of_movedTo q PP hPP V β b g _ _ hb hM hSt a a' z hz.symm
  simpa [Matrix.submatrix_apply] using key

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (q.pr.comp (incA D)) ϖ → ∀ (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) (σ : Fin V.rank ≃ Y) (b : GA D V), MovedTo (ofSplit q) V b β (F.β.submatrix id σ) → ∀ (g : GA D V) (gk : GL Y k), (ofSplit q).IsLoc F g gk → Lev.finE V (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → ∀ (a a' : Fin V.rank) (z : 𝓞 D.host.E), (Formalism.L2.DIV.redFn β PP (Lev.finE V (b⁻¹ * g * b))).val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (gk.val (σ a) (σ a') - (ofSplit q).pr (z : D.host.E)) < 1 := by
  atlas_forward_decl GlobalTheory.LocRed.red_entry_movedFrame
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section
namespace GlobalTheory.TwLevRed

theorem reGL_symm_mem_KO_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem blockTri_iff_mem_lev : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  intro E _ _ k _ _ _ _ PP ι hPP K T s j d hd δ hδ η n e he x hx R hR
  have hent : ∀ a b, R.val a b = 0 ↔ valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a))
      (stdOrd (Fin K) (Fin T) j d hd (e.symm b))) < 1 := by
    intro a b
    constructor
    · intro h0
      have := hR a b 0 (by rw [h0, map_zero])
      simpa using this
    · intro hv
      obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (R.val a b)
      have h1 := hR a b z hz.symm
      have h2 : valuation k (ι (z : E)) < 1 := by
        have : ι (z : E) = x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) -
            (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm b)) - ι (z : E)) := by
          ring
        rw [this]
        exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hv h1)
      rw [← hz, Ideal.Quotient.eq_zero_iff_mem]
      exact hPP z h2
  have hblk : ∀ q : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j,
      Formalism.L2.DIV.blk2 (K + (s + 1)) (e q) = Sum.elim (fun _ => 0) (fun _ => 1) q := by
    intro q
    have h := he q
    unfold Formalism.L2.DIV.blk2
    rcases q with (i | i) | p
    · have : (e (.inl (.inl i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : (e (.inl (.inr i))).val < K + (s + 1) := by rw [h]; simp [GlobalTheory.SymBridge.zPos]; omega
      simp [this]
    · have : ¬ (e (.inr p)).val < K + (s + 1) := by
        rw [h, not_lt]; simp only [GlobalTheory.SymBridge.zPos]
        exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
      simp [this]
  have hJ : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J ↔
      ∀ (p : Fin j × Fin T) (i : Fin K ⊕ Fin (s + 1)),
        valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inl i))) < 1 := by
    change (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J ↔ _
    rw [mem_parahoric]
    have e' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x =
        (reGL (stdOrd (Fin K) (Fin T) j d hd)).symm x := by
      simp [LatFrame.conj, plainFrame]
      rfl
    rw [e', reGL_symm_mem_KO_iff]
    simp only [hx, true_and]
    rfl
  rw [hJ, Formalism.L2.DIV.mem_blockTri]
  constructor
  · intro h p i
    have := h (e (.inr p)) (e (.inl i)) (by rw [hblk, hblk]; simp)
    rw [hent] at this
    simpa using this
  · intro h a b hab
    obtain ⟨q, rfl⟩ := e.surjective a
    obtain ⟨q', rfl⟩ := e.surjective b
    rw [hblk, hblk] at hab
    rw [hent]
    rcases q with q | q <;> rcases q' with q' | q' <;> simp at hab
    simpa using h q q'

end GlobalTheory.TwLevRed
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k), x ∈ KO k _ → ∀ (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → (R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) ↔ x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) := by
  atlas_forward_decl GlobalTheory.TwLevRed.blockTri_iff_mem_lev
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.LevChr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {A B : Matrix m m k} (hA : IntM A) (hB : IntM B)
    (h : MaxM (A - B)) : valuation k (A.det - B.det) < 1 := by
  let A' : Matrix m m 𝒪[k] := fun i j => ⟨A i j, hA i j⟩
  let B' : Matrix m m 𝒪[k] := fun i j => ⟨B i j, hB i j⟩
  have eA : A.det = ((A'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) A'.det
    rw [RingHom.map_det]; rfl
  have eB : B.det = ((B'.det : 𝒪[k]) : k) := by
    change _ = (algebraMap 𝒪[k] k) B'.det
    rw [RingHom.map_det]; rfl
  rw [eA, eB, ← residue_eq_iff_lt, RingHom.map_det, RingHom.map_det]
  congr 1
  ext i j
  exact (residue_eq_iff_lt (A' i j) (B' i j)).2 (by simpa using h i j)

end GlobalTheory.LevChr

namespace GlobalTheory.LevChr

theorem secondBlockIndex_eq_one_iff_basisNumbering {K s T j n : ℕ} {e : StepData.Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n}
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e) (a : Fin n) :
    Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ∃ p, e.symm a = .inr p := by
  have h0 := he (e.symm a)
  rw [e.apply_symm_apply] at h0
  have hb : Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1 ↔ ¬ a.val < K + (s + 1) := by
    unfold Formalism.L2.DIV.blk2; split_ifs with h <;> simp [h]
  rw [hb]
  rcases hc : e.symm a with (i | i) | p <;> rw [hc] at h0 <;> simp only [GlobalTheory.SymBridge.zPos] at h0
  · have := i.2; simp; omega
  · have := i.2; simp; omega
  · simp; omega

end GlobalTheory.LevChr

theorem GlobalTheory.LevChr.lam_eq_inv_xi : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  intro E _ _ k _ _ _ _ PP ι _h1 _h2 K T s j d hd δ hδ η ξ hRes n e he x hx R hR hTri
  have hx' : (plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x ∈
      (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).J := hx
  change _ = (parahoric (Fin K ⊕ Fin (s + 1)) (Fin j × Fin T) δ hδ).lam ⟨_, hx'⟩
  obtain ⟨hKO, hC⟩ := mem_parahoric.1 hx'
  obtain ⟨-, D, hD, hDv⟩ := exists_diag_blocks hKO hC
  rw [parahoric_lam ⟨_, hx'⟩ D hDv]
  have hy : ((plainFrame (k := k) (stdOrd (Fin K) (Fin T) j d hd)).conj.symm x).val =
      x.val.submatrix (stdOrd (Fin K) (Fin T) j d hd) (stdOrd (Fin K) (Fin T) j d hd) := by
    change ((reGL (stdOrd (Fin K) (Fin T) j d hd)).symm
      ((MulAut.conj (1 : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k)).symm x)).val = _
    rw [reGL_symm_val, MulAut.conj_symm_apply]
    simp
  have hDe : ∀ p p', D.val p p' =
      x.val (stdOrd (Fin K) (Fin T) j d hd (.inr p)) (stdOrd (Fin K) (Fin T) j d hd (.inr p')) := by
    intro p p'; rw [hDv, hy]; rfl

  have hb := GlobalTheory.LevChr.secondBlockIndex_eq_one_iff_basisNumbering he
  let f : Fin j × Fin T ≃ {a : Fin n // Formalism.L2.DIV.blk2 (K + (s + 1)) a = 1} :=
    Equiv.ofBijective (fun p => ⟨e (.inr p), (hb _).2 ⟨p, by simp⟩⟩)
      ⟨fun p p' h => Sum.inr_injective (e.injective (congrArg Subtype.val h)), fun a => by
        obtain ⟨p, hp⟩ := (hb a.1).1 a.2
        exact ⟨p, Subtype.ext (by simp [← hp])⟩⟩

  choose Z hZ using fun a a' => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (R.val a a')
  let Zf : Matrix (Fin j × Fin T) (Fin j × Fin T) (𝓞 E) := fun p p' => Z (e (.inr p)) (e (.inr p'))
  have hdet : ((Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R : (𝓞 E ⧸ PP.asIdeal)ˣ) : 𝓞 E ⧸ PP.asIdeal) =
      Ideal.Quotient.mk PP.asIdeal Zf.det := by
    rw [Formalism.L2.DIV.diag_block_det_val 1 hTri, ← Matrix.det_submatrix_equiv_self f, RingHom.map_det]
    congr 1
    ext p p'
    show R.val (e (.inr p)) (e (.inr p')) = Ideal.Quotient.mk PP.asIdeal (Z (e (.inr p)) (e (.inr p')))
    rw [hZ]

  have hA : IntM D.val := intM_of_mem_KO hD
  have hM : MaxM (D.val - (ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := hR (e (.inr p)) (e (.inr p')) _ (hZ _ _).symm
    simp only [Equiv.symm_apply_apply] at h
    show valuation k (D.val p p' - ι (Z (e (.inr p)) (e (.inr p')) : E)) < 1
    rw [hDe]; exact h
  have hB : IntM ((ι.comp (algebraMap (𝓞 E) E)).mapMatrix Zf) := fun p p' => by
    have h := sub_mem (hA p p') (hM.intM p p')
    simpa using h
  have hlt := GlobalTheory.LevChr.det_sub_lt hA hB hM
  rw [← RingHom.map_det] at hlt
  have hlt' : valuation k (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) < 1 := by
    rw [Matrix.GeneralLinearGroup.val_det_apply]; exact hlt
  have hv1 : valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) = 1 := valuation_det_of_mem_KO hD
  have hvz : valuation k (ι (Zf.det : E)) = 1 := by
    have h : valuation k (ι (Zf.det : E) - (Matrix.GeneralLinearGroup.det D : kˣ)) <
        valuation k ((Matrix.GeneralLinearGroup.det D : kˣ) : k) := by
      rw [hv1, ← Valuation.map_neg, neg_sub]; exact hlt'
    rw [Valuation.map_eq_of_sub_lt _ h, hv1]
  have hz0 : ι (Zf.det : E) ≠ 0 := by
    intro h; rw [h, map_zero] at hvz; exact zero_ne_one hvz
  set u : kˣ := Units.mk0 (ι (Zf.det : E)) hz0 with hu
  have htame : δ (u⁻¹ * Matrix.GeneralLinearGroup.det D) = 1 := by
    apply hδ
    have e1 : ((u⁻¹ * Matrix.GeneralLinearGroup.det D : kˣ) : k) - 1 =
        (ι (Zf.det : E))⁻¹ * (((Matrix.GeneralLinearGroup.det D : kˣ) : k) - ι (Zf.det : E)) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, Units.val_mk0, mul_sub, inv_mul_cancel₀ hz0]
    rw [e1, map_mul, map_inv₀, hvz, inv_one, one_mul]; exact hlt'
  rw [show Matrix.GeneralLinearGroup.det D = u * (u⁻¹ * Matrix.GeneralLinearGroup.det D) by group, map_mul, htame,
    mul_one]
  exact (hRes Zf.det u _ (by rw [hu, Units.val_mk0]) hdet).symm
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) → (∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1) → ∀ (K T s j d : ℕ) (hd : j + d = s + 1) (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (ξ : (𝓞 E ⧸ PP.asIdeal)ˣ →* ℂˣ), (∀ (z : 𝓞 E) (u : kˣ) (r : (𝓞 E ⧸ PP.asIdeal)ˣ), (u : k) = ι z → (r : 𝓞 E ⧸ PP.asIdeal) = Ideal.Quotient.mk PP.asIdeal z → δ u = (ξ r)⁻¹) → ∀ (n : ℕ) (e : Ix (Fin K ⊕ Fin (s + 1)) (Fin T) j ≃ Fin n), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos e → ∀ (x : GL (XIx (Fin K) (Fin T) j ⊕ Fin d) k) (hx : x ∈ ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).J) (R : GL (Fin n) (𝓞 E ⧸ PP.asIdeal)), (∀ (a a' : Fin n) (z : 𝓞 E), R.val a a' = Ideal.Quotient.mk PP.asIdeal z → valuation k (x.val (stdOrd (Fin K) (Fin T) j d hd (e.symm a)) (stdOrd (Fin K) (Fin T) j d hd (e.symm a')) - ι z) < 1) → R ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (K + (s + 1))) → (ξ (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 (K + (s + 1))) 1 R))⁻¹ = ((twistChain s (Fin T) (Fin K) δ hδ η).lev j d hd).lam ⟨x, hx⟩ := by
  atlas_forward_decl GlobalTheory.LevChr.lam_eq_inv_xi
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SymBridge.ComplDense

theorem small_in_prime_and_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  intro E _ _ k _ _ _ _ PP q ι ϖ h hu
  refine ⟨fun z hz => (GlobalTheory.SymBridge.ComplRes.mem_P_iff h hu z).mpr hz, fun y hy => ?_⟩
  obtain ⟨i, -, hv⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep_one h hu y ((Valuation.mem_integer_iff _ _).mp hy)
  refine ⟨(i : 𝓞 E), ?_⟩
  have e : ι (((i : ℕ) : 𝓞 E) : E) = (i : k) := by simp
  rw [e]
  exact lt_of_le_of_lt hv (GlobalTheory.SymBridge.ComplRes.v_unif_lt_one hu)

end GlobalTheory.SymBridge.ComplDense
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_smallIntegers_in_prime_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  atlas_forward_decl GlobalTheory.SymBridge.ComplDense.small_in_prime_and_dense
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LevGlue

theorem mem_levS_datY_single : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F)) → (∀ PP' ∈ Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  intro D V β r t j hr Pg Q P χ ξ PP hPQ hPg hQ κ hκ hoff
  have hPgoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Pg, Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP => hoff PP' (hPg PP' hP) hSt
  have hQoff : Lev.finE V κ ∈ Formalism.L2.DIV.St β → ∀ PP' ∈ Q, PP' ≠ PP → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1 :=
    fun hSt PP' hP hne => hoff PP' (fun e => hne (hQ PP' hP e)) hSt
  have hrt : Lev.finE V κ ∈ Formalism.L2.DIV.St β →
      Formalism.L2.DIV.rTup β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) (Lev.finE V κ) = 1 := by
    intro hSt
    funext PP'
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn β PP'.1 _) = 1
    rw [hPgoff hSt _ PP'.2]
    exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  refine ⟨⟨fun h => ?_, fun ⟨hSt, hP⟩ => ?_⟩, fun hSt => ?_⟩
  · have h' : κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) := h
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev] at h'
    obtain ⟨_, ⟨_, hSt, _, hq⟩, _⟩ := h'
    exact ⟨hSt, hq PP hPQ⟩
  · show κ ∈ Lev.levG V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B)
    rw [Lev.levG, Lev.levA, Subgroup.mem_inf, Subgroup.mem_comap, Formalism.L2.DIV.mem_lev, Formalism.L2.DIV.mem_parLev]
    refine ⟨hκ, ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, ?_, ?_⟩, ?_⟩
    · intro PP' hP'
      rw [hPgoff hSt PP' hP']
      exact one_mem _
    · intro PP' hP'
      by_cases e : PP' = PP
      · rw [e]
        exact hP
      · rw [hQoff hSt PP' hP' e]
        exact one_mem _
    · rw [hrt hSt]
      exact one_mem _
  · simp only [Lev.levChi]
    congr 1
    simp only [Formalism.L2.DIV.levFn]
    rw [hrt hSt, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul]
    rw [Finset.prod_eq_one (fun PP' hP' => Finset.prod_eq_one fun c _ => by
      rw [hPgoff hSt PP' hP', Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]), one_mul]
    rw [Finset.prod_eq_single_of_mem (s := (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B).Q) PP hPQ fun PP' hP hne => by
      rw [hQoff hSt PP' hP hne, Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]]
    simp [Lev.datY]

end GlobalTheory.LevGlue

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_twistPlaceLevel_single_place_character : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (r t j : ℕ) (hr : r ≤ V.rank) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (PP : Formalism.L2.DIV.Pl D.host.E), PP ∈ Q → (∀ PP' ∈ Pg, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F)) → (∀ PP' ∈ Q, PP'.under (𝓞 D.host.F) = PP.under (𝓞 D.host.F) → PP' = PP) → ∀ (κ : GA D V), κ ∈ GfC V → (∀ PP' : Formalism.L2.DIV.Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) → Lev.finE V κ ∈ Formalism.L2.DIV.St β → Formalism.L2.DIV.redFn β PP' (Lev.finE V κ) = 1) → (κ ∈ levS V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) ↔ Lev.finE V κ ∈ Formalism.L2.DIV.St β ∧ Formalism.L2.DIV.redFn β PP (Lev.finE V κ) ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) ∧ (Lev.finE V κ ∈ Formalism.L2.DIV.St β → Lev.levChi V β (Lev.datY V.rank r t j hr Pg Q P χ ξ Lev.Frm.B) κ = (((ξ PP (Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 r) 1 (Formalism.L2.DIV.redFn β PP (Lev.finE V κ))))⁻¹ : ℂˣ) : ℂ)) := by
  atlas_forward_decl GlobalTheory.LevGlue.mem_levS_datY_single
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.QLevMid

set_option maxHeartbeats 2000000 in

theorem level_at_place : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ (t : W.P.T) (PP : Formalism.L2.DIV.Pl (I.rec7 l Z).host.E) (hP : PP ∈ (pk W).Q t) (E : QExt (a.Q PP ⟨t, hP⟩) (chrK W t)), (a.Q PP ⟨t, hP⟩).Res E.δ ((pk W).xiR t PP) → ∀ (j d : ℕ) (hd : j + d = (a.Q PP ⟨t, hP⟩).s + 1), j < (I.rec7 l Z).R.m → ∀ x ∈ GlobalTheory.SplitWeil.KO (a.Q PP ⟨t, hP⟩).k (GlobalTheory.StepData.XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ⊕ Fin d), ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j ∈ levS (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ↔ x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J) ∧ ∀ hx : x ∈ (((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).J, Lev.levChi (Yc (I.rec7 l Z) j) ((pk W).βY j) ((pk W).datYt t j (lvP W)) ((a.g.b j)⁻¹ * (a.Q PP ⟨t, hP⟩).gl j d hd x * a.g.b j) = ((((a.Q PP ⟨t, hP⟩).T E.δ E.tame E.η).lev j d hd).lam ⟨x, hx⟩ : ℂ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT t PP hP E hRes j d hd hj x hxK
  obtain ⟨⟨N, hSD⟩, hPg⟩ := GlobalTheory.T.true_pack_twist_place_property W hW t PP hP j hj
  obtain ⟨e, he, hmv⟩ := (a.Q PP ⟨t, hP⟩).frame j d hd
  have hloc := (a.Q PP ⟨t, hP⟩).gl_loc j d hd x
  obtain ⟨hG, hSt, hOff⟩ := GlobalTheory.T.splitPlace_conj_stabilizes_framedLattice_iff _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  have hRed := GlobalTheory.T.reduction_conjugated_eq_movedFrame_matrix _ _ (a.Q PP ⟨t, hP⟩).q PP (a.Q PP ⟨t, hP⟩).idem _ (a.Q PP ⟨t, hP⟩).compl _ _ _ N hSD _ _ (e.symm.trans (stdOrd _ _ j d hd)) _ hmv _ _ hloc
  obtain ⟨hι, hrep⟩ := GlobalTheory.T.completion_smallIntegers_in_prime_dense _ _ PP _ _ _ (a.Q PP ⟨t, hP⟩).compl (a.Q PP ⟨t, hP⟩).unif
  have hSt' := hSt.2 hxK

  have hQ : ∀ PP' ∈ (pk W).Q t, PP'.under (𝓞 (I.rec7 l Z).host.F) = PP.under (𝓞 (I.rec7 l Z).host.F) → PP' = PP :=
    fun PP' hP' h => hW.pk.sel PP' PP ⟨t, hP'⟩ ⟨t, hP⟩ h
  obtain ⟨hmem, hchi⟩ := GlobalTheory.T.mem_twistPlaceLevel_single_place_character _ _ ((pk W).βY j) (I.rec7 l Z).R.r (I.rec7 l Z).R.t j (r_le_Y j) (pk W).Pg ((pk W).Q t) (lvP W) (pk W).chi ((pk W).xiR t) PP hP hPg hQ _ hG hOff
  have hr : (I.rec7 l Z).R.r = (I.rec7 l Z).R.k + ((a.Q PP ⟨t, hP⟩).s + 1) := by
    have := (a.Q PP ⟨t, hP⟩).hs
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hC1 := GlobalTheory.T.reductionBlockTriangular_iff_mem_parahoricLevel _ _ PP _ hι (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η _ e he x hxK _ (hRed hSt')
  have hC2 := GlobalTheory.T.parahoricLevelCharacter_eq_inv_blockDet _ _ PP _ hι hrep (I.rec7 l Z).R.k (I.rec7 l Z).R.t (a.Q PP ⟨t, hP⟩).s j d hd E.δ E.tame E.η ((pk W).xiR t PP) hRes _ e he x
  rw [← hr] at hC1 hC2
  refine ⟨hmem.trans ⟨fun h => hC1.1 h.2, fun h => ⟨hSt', hC1.2 h⟩⟩, fun hx => ?_⟩
  exact (hchi hSt').trans (congrArg Units.val (hC2 hx _ (hRed hSt') (hC1.2 hx)))

end GlobalTheory.QLevMid

end
end
