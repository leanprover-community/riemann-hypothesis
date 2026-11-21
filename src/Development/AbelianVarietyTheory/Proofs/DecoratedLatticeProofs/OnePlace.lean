import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.BesselCompatibility
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEdge
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReductionStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PinnedLocalGroupsHaveLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingMemFiniteAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelSubgroupConjFiniteMovesFrame
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelZeroStabilizerMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdeleProjectionIntegralReduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelZeroUniformizerFrameUnipotentAndEmbedGL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralFramePointOfInertHalfLatticePoint
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualTypeResidueCharsUnramifiedTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramAtOfUnramOutside

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_level_zero_stabilizer_mem : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP), d.Base → ∀ (hr : D.R.r ≤ (d.st 0).V.rank) (g : GA D (d.st 0).V) (x : G.S.P.J), (GlobalTheory.LocMod.ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0) ∈ St (d.st 0).β → G.Red x (upperLeftBlock hr (redFn (d.st 0).β PP (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)))) := by
  first | exact @GlobalTheory.LevZeroRead.red_of_isLoc | exact GlobalTheory.LevZeroRead.red_of_isLoc | (intros; apply GlobalTheory.LevZeroRead.red_of_isLoc <;> assumption)
end

section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceRed

theorem pr_add_conj_eq_zero {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (a : Formalism.L2.Theta.AE D)
    (h : a * (q.e + cA D q.e) = 0) : q.pr a = 0 := by
  have h1 : q.pr q.e = 1 := by
    have h2 := q.pr_sec 1
    have h3 := q.sec_pr 1
    rw [map_one, mul_one] at h3
    rwa [h3] at h2
  have h4 : q.pr (cA D q.e) = 0 := by
    have := congrArg q.pr q.split.2.1
    rwa [map_mul, h1, one_mul, map_zero] at this
  have := congrArg q.pr h
  rwa [map_mul, map_add, h1, h4, add_zero, mul_one, map_zero] at this

theorem bc_eq_one_of_isRed {S κ k : Type} [CommRing S] [CommRing κ] [Field k] [ValuativeRel k] {φ : S →+* κ}
    {ψ : S →+* k} (hred : GlobalTheory.FunObj.Comparison₂.IsRed φ ψ) {n : ℕ} (m : GL (Fin n) S) (h : Formalism.UG.bc ψ m = 1) :
    Formalism.UG.bc φ m = 1 := by
  apply Units.ext
  ext i j
  have h6 : ψ (m.val i j) = (1 : Matrix (Fin n) (Fin n) k) i j :=
    congrArg (fun x : GL (Fin n) k => x.val i j) h
  show φ (m.val i j) = (1 : Matrix (Fin n) (Fin n) κ) i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq] at h6 ⊢
    have h7 := (hred.ker (m.val i i - 1)).2 (by
      rw [map_sub, map_one, h6, sub_self, map_zero]; exact zero_lt_one)
    rwa [map_sub, map_one, sub_eq_zero] at h7
  · rw [Matrix.one_apply_ne hij] at h6 ⊢
    refine (hred.ker (m.val i j)).2 ?_
    rw [h6, map_zero]; exact zero_lt_one

theorem bc_comp_eq_one {S A k : Type} [CommRing S] [CommRing A] [CommRing k] (ι : S →+* A) (π : A →+* k) {n : ℕ}
    (m : GL (Fin n) S) (β x : GL (Fin n) A) (hx : β * Formalism.UG.bc ι m * β⁻¹ = x) (h : Formalism.UG.bc π x = 1) :
    Formalism.UG.bc (π.comp ι) m = 1 := by
  rw [← hx, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
  exact h

theorem redFn_eq_one_of_suppAt : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  intro D k _ _ _ _ q PP hq e he V β g hg hst
  obtain ⟨π', hπ, hred, -, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D k q PP hq
  obtain ⟨m, hm⟩ := hst
  have h0 : q.pr (e + cA D e) = 0 := pr_add_conj_eq_zero q _ he
  have h1 : (finE V g).val.map π' = 1 := by
    ext i j
    have h2 : q.pr ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
      rw [← hg i j, map_mul, h0, zero_mul]
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h2
    show π' (toEAf D (Formalism.L2.Theta.mt V g i j)) = _
    rw [hπ, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have h3 : Formalism.UG.bc π' (finE V g) = 1 := Units.ext h1
  rw [← hm, redFn_frGL]
  exact bc_eq_one_of_isRed hred m (bc_comp_eq_one _ π' m β _ hm h3)

end GlobalTheory.OffPlaceRed

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ (e : Formalism.L2.Theta.AE D), (e + cA D e) * (q.e + cA D q.e) = 0 → ∀ (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (g : GA D V), Formalism.L2.Theta.SuppAt e V g → finE V g ∈ St β → redFn β PP (finE V g) = 1 := by
  atlas_forward_decl GlobalTheory.OffPlaceRed.redFn_eq_one_of_suppAt
end

section
section
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.SymChain.SymData
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

theorem exists_N_embX_inv_mul_mem_KOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ)
      (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k),
        n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧
        (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  intro k _ _ _ _ s κ S x hx
  obtain ⟨hxK, hpat⟩ := (mem_J_iff_pattern k s κ S x).1 hx
  set M : Matrix (Fin κ ⊕ Fin (s + 1)) (Fin κ ⊕ Fin (s + 1)) k :=
    fun a b => if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b with hMdef
  have hMax : MaxM (M - x.val) := by
    intro a b
    show valuation k ((if FreeTop S.ρ a b then x.val a b else (1 : Matrix _ _ k) a b) - x.val a b) < 1
    split_ifs with h
    · simp
    · rw [Valuation.map_sub_swap]; exact hpat a b h
  obtain ⟨u, hu, hMu⟩ := exists_mul_KOne hxK hMax
  have hMK : x * u ∈ KO k _ := mul_mem hxK (KOne_le_KO hu)
  have hpatM : ∀ a b, ¬ FreeTop S.ρ a b → (x * u).val a b = (1 : Matrix _ _ k) a b := by
    intro a b h; rw [hMu]; simp [hMdef, h]
  obtain ⟨n, hn, γ, hγ, e⟩ := GlobalTheory.SymPattern.exists_of_pat S.ρ (x * u) hpatM

  have hγv : ∀ i j, γ.val i j = (x * u).val (Sum.inl i) (Sum.inl j) := by
    intro i j
    rw [e, Units.val_mul, Radical.embX_val, GlobalTheory.SymPattern.mul_fromBlocks_inl]
    have e1 : ∀ t, n.val (Sum.inl i) (Sum.inl t) = (1 : Matrix (Fin κ) (Fin κ) k) i t := by
      intro t
      rw [hn _ _ (by simp [lev])]
      simp [Matrix.one_apply]
    simp only [e1]
    rw [← Matrix.mul_apply, Matrix.one_mul]
  have hγint : ∀ i j, γ.val i j ∈ 𝒪[k] := fun i j => by
    rw [hγv]; exact intM_of_mem_KO hMK _ _

  have hγK : γ ∈ KO k (Fin κ) := by
    let A₀ : Matrix (Fin κ) (Fin κ) 𝒪[k] := fun i j => ⟨γ.val i j, hγint i j⟩
    have hmap : (algebraMap 𝒪[k] k).mapMatrix A₀ = γ.val := by ext i j; rfl
    have hdet1 : γ.val.det = 1 := Radical.Uni.det (b := Fin.val) hγ
    have hdet : A₀.det = 1 := by
      apply Subtype.ext
      have := RingHom.map_det (algebraMap 𝒪[k] k) A₀
      rw [hmap, hdet1] at this
      simpa using this
    refine ⟨Matrix.nonsingInvUnit A₀ (by rw [hdet]; exact isUnit_one), ?_⟩
    ext i j
    rfl
  have hembK : embX (s + 1) γ ∈ KO k _ := by
    refine mem_KO.2 ⟨?_, ?_⟩
    · rw [Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO hγK, intM_zero, intM_zero, intM_one⟩
    · rw [← map_inv, Radical.embX_val]
      exact intM_fromBlocks.2 ⟨intM_of_mem_KO (inv_mem hγK), intM_zero, intM_zero, intM_one⟩
  have hnK : n ∈ KO k _ := by
    have : n = (x * u) * (embX (s + 1) γ)⁻¹ := by rw [e]; group
    rw [this]; exact mul_mem hMK (inv_mem hembK)
  refine ⟨n, γ, (Radical.mem_N_iff n).2 hn, ?_, ?_, ?_⟩
  · refine (mem_J_iff_pattern k s κ S n).2 ⟨hnK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ n hn 1 (fun r s _ => rfl) a b hab
    rw [map_one, mul_one] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · refine (mem_J_iff_pattern k s κ S _).2 ⟨hembK, fun a b hab => ?_⟩
    have h1 := GlobalTheory.SymPattern.pat_of_mul S.ρ 1 (fun r s _ => rfl) γ hγ a b hab
    rw [one_mul] at h1
    rw [h1, sub_self, map_zero]; exact zero_lt_one
  · rw [← e, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
    exact inv_mem hu

end GlobalTheory.SymChain.SymData
end
end

open ValuativeRel Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ), ∀ x ∈ S.P.J, ∃ (n : GL (Fin κ ⊕ Fin (s + 1)) k) (γ : GL (Fin κ) k), n ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) ∧ n ∈ S.P.J ∧ GlobalTheory.RootEx.embX (s + 1) γ ∈ S.P.J ∧ (n * GlobalTheory.RootEx.embX (s + 1) γ)⁻¹ * x ∈ GlobalTheory.SplitWeil.KOne k (Fin κ ⊕ Fin (s + 1)) := by
  atlas_forward_decl GlobalTheory.SymChain.SymData.exists_N_embX_inv_mul_mem_KOne
end

section
open ValuativeRel Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  first | exact @GlobalTheory.LevZeroUp.upZero_N_embX | exact GlobalTheory.LevZeroUp.upZero_N_embX | (intros; apply GlobalTheory.LevZeroUp.upZero_N_embX <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocGrp
open GlobalTheory.LocMod GlobalTheory.RootEx GlobalTheory.SplitWeil

theorem isLoc_embA : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ (h : GA D B.A) (γ : GL n k), p.IsLoc FA h γ → p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c γ) := by
  intro D k _ _ _ _ p n _ _ c ρ B s FA F hF h γ hh
  obtain ⟨rfl, h0, hX, hz, hY⟩ := hF
  rw [embA_apply]
  have eA : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jA) = B.d.j0 ⬝ B.o.jA ⬝ mt B.A h := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jA, Matrix.mul_assoc]
  have eB : mt B.V (B.d.emb0 (B.o.emb (h, 1))) ⬝ (B.d.j0 ⬝ B.o.jB) = B.d.j0 ⬝ B.o.jB := by
    rw [cancel₂ (B.d.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, B.o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  have rA : B.d.j0 ⬝ B.o.jA = rat (B.d.i₀ * B.o.iA) := (rat_mul _ _).symm
  have rB : B.d.j0 ⬝ B.o.jB = rat (B.d.i₀ * B.o.iB) := (rat_mul _ _).symm
  rw [rA] at eA
  rw [rB] at eB
  refine ⟨suppAt_wittLeviEmbedding B.d (suppAt_emb B.o hh.1),
    eq_embX F _ γ ((rat (B.d.i₀ * B.o.iA)).map p.π * FA.β) h0 (intertwine p eA hh) fun j => ?_⟩
  rcases lt_trichotomy j.val ρ with hj | hj | hj
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (hX _ j rfl)
  · refine fix_vec (map_fix p eB) s (Witness.prH p ∘ B.ζ) fun r => (hz j hj r).trans (congrArg (s * ·) ?_)
    rw [vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec (Witness.prH p) _ _ r
  · exact fix_col (map_fix p (B.d.wittDecomp_anisotropicEmbedding_inclY _)) _ ⟨2 * ρ - j.val, by omega⟩ (hY _ j (by simp only; omega))

end GlobalTheory.LocGrp
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFrame_embedding_localElement_eq_embedded_matrix : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ (h : GA D B.A) (γ : GL n k), p.IsLoc FA h γ → p.IsLoc F (embA B.d B.o h) (GlobalTheory.RootEx.embX c γ) := by
  atlas_forward_decl GlobalTheory.LocGrp.isLoc_embA
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PlaceMatch

theorem mem_GfC_of_suppAt' {D : D7} {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  obtain ⟨-, -, v, ε, ⟨α, rfl, -⟩, h⟩ := he
  have h0 : infPart D (e + cA D e) = 0 := by
    rw [h]; exact TensorProduct.zero_tmul _ _
  refine Units.ext (Matrix.ext fun i j => ?_)
  have := congrArg (infPart D) (hg i j)
  rw [map_mul, h0, zero_mul, Matrix.sub_apply, map_sub, eq_comm, sub_eq_zero] at this
  refine Eq.trans this ?_
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem suppAt_conj' {D : D7} {e : Formalism.L2.Theta.AE D} {V : HSp D} {g : GA D V} (hg : Formalism.L2.Theta.SuppAt e V g) (t : GA D V) :
    Formalism.L2.Theta.SuppAt e V (t⁻¹ * g * t) := by
  refine GlobalTheory.LocGrp.suppAt_of_sandwich hg (mt V t⁻¹) (mt V t) ?_
  rw [GlobalTheory.MixModel.mt_mul, GlobalTheory.MixModel.mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, GlobalTheory.MixModel.mt_inv_mul]

theorem finE_mem_St_of_lev {D : D7} {u : D.what₂.Word} (d : GlobalTheory.SeeSaw.Dat D u) (hB : d.Base) (g : GA D (d.st 0).V)
    (hg : g ∈ d.lev 0) : finE (d.st 0).V g ∈ St (d.st 0).β := by
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨hr', ξ, hL⟩ := (hB.st 0 hm).lev
  have h1 : g ∈ GfC _ ∧ finE (d.st 0).V g ∈ lev D.sp.cm (d.st 0).V.gram (d.st 0).β (d.st 0).L := hg
  rw [hL, mem_lev, mem_parLev] at h1
  exact h1.2.1.2.1

theorem red_of_congr {D : D7} {u : D.what₂.Word} {d : GlobalTheory.SeeSaw.Dat D u}
    {τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E} {PP : Pl D.host.E}
    (G : GlobalTheory.LocMod.GAt d τ PP) (x x' : G.S.P.J) (g : GL (Fin D.R.r) (kP PP)) (h : G.Red x' g)
    (hc : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 ∈ GlobalTheory.SplitWeil.KOne G.k (Fin D.R.k ⊕ Fin (G.s + 1))) :
    G.Red x g := by
  intro a b a' b' ha hb z hz
  have h1 := h a b a' b' ha hb z hz
  have hI : GlobalTheory.StepData.IntM (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val :=
    GlobalTheory.StepData.intM_of_mem_KO (G.S.P.le_KO x'.2)
  have hM := hI.mul_maxM (GlobalTheory.StepData.mem_KOne.1 hc)
  have e : (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val *
      (((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k)⁻¹ * x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - 1) =
      (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val := by
    rw [Matrix.mul_sub, Units.val_mul, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_one]
  rw [e] at hM
  have h2 := hM a b
  rw [Matrix.sub_apply] at h2
  have e2 : (x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) =
      ((x.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b) +
      ((x'.1 : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E)) := by ring
  rw [e2]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h2 h1)

end GlobalTheory.PlaceMatch

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.PlaceMatch.one_place : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (G : ∀ PP : d.c.Pg, GlobalTheory.LocMod.GAt d τ PP.1) (cG : ∀ j, WO (D.sp.X j) (D.sp.X (j + 1)) →₀ ℂ) (h0 : 0 + 2 * D.R.rS + 2 = D.R.m), d.Base → IsTypePlaces d.c.Pg → GlobalTheory.LocMod.PinGBy G cG → ∀ Q : GA D (d.st 0).V → Prop, (∀ k ∈ d.lev 0, ∀ k' ∈ d.lev 0, Q k → Q k' → Q (k * k')) → (∀ (PP : d.c.Pg) (n : GA D (d.st 0).V) (q : GL (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin ((G PP).s + 1)) (G PP).k), n ∈ flagN (d.bes 0 D.R.rS h0).d → q ∈ GlobalTheory.RootEx.N (G PP).k _ ((G PP).s + 1) (D.R.rS + 1) → (GlobalTheory.LocMod.ofSplit (G PP).q).IsLoc ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) n q → (d.t 0)⁻¹ * n * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * n * d.t 0)) → (∀ b ∈ GfC (D.sp.X 0), (d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0 ∈ d.lev 0 → Q ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o b * d.t 0)) → ∀ (PP : d.c.Pg) (x : (G PP).S.P.J), ∃ m ∈ d.lev 0, Q m ∧ (∀ hr : D.R.r ≤ (d.st 0).V.rank, (G PP).Red x (upperLeftBlock hr (redFn (d.st 0).β PP.1 (finE (d.st 0).V m)))) ∧ ∀ PP' ∈ d.c.Pg, PP' ≠ PP.1 → redFn (d.st 0).β PP' (finE (d.st 0).V m) = 1 := by
  intro D u d τ G cG h0 hB _hTP hG Q hmul hN hU PP x
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hn : (d.st 0).V.rank = D.R.r := by rw [(hB.st 0 hm).rank]; show D.R.r + 0 * D.R.t = D.R.r; simp
  have hst : ∀ w ∈ d.lev 0, finE (d.st 0).V w ∈ St (d.st 0).β := GlobalTheory.PlaceMatch.finE_mem_St_of_lev d hB
  have hbes := (G PP).bes 0 D.R.rS h0 ((G PP).s + 1) (Nat.zero_add _)
  have hρ : (G PP).S.ρ = D.R.rS := by have := hbes.1; have := (G PP).S.odd; omega
  have hLev := GlobalTheory.T.pinned_local_groups_have_level D u d τ cG G hB hG PP 0 ((G PP).s + 1) (Nat.zero_add _)
  have hv : ∀ P : d.c.Pg, (G P).q.v = IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers D.host.F) P.1 := by
    intro P
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    exact (GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ P.1 _ ε (G P).idem hε hsum).symm
  have horth : ∀ P P' : d.c.Pg, P ≠ P' →
      ((G P).q.e + cA D (G P).q.e) * ((G P').q.e + cA D (G P').q.e) = 0 := by
    intro P P' hne
    obtain ⟨ε, hε, hsum⟩ := (G P).q.above
    obtain ⟨ε', hε', hsum'⟩ := (G P').q.above
    have hvv : (G P).q.v ≠ (G P').q.v := by
      rw [hv P, hv P']
      intro h
      exact hne (Subtype.ext (GlobalTheory.LevelPlaces.injOn_under D d.c hB.com P.2 P'.2 h))
    rw [hsum, hsum', ← map_mul, GlobalTheory.SingleDatum.BasePair.placeIdem_mul_eq_zero hε' hε hvv, map_zero]
  have hoff : ∀ g : GA D (d.st 0).V, Formalism.L2.Theta.SuppAt (G PP).q.e (d.st 0).V g → (d.t 0)⁻¹ * g * d.t 0 ∈ d.lev 0 →
      ∀ PP' ∈ d.c.Pg, PP' ≠ PP.1 → redFn (d.st 0).β PP' (finE (d.st 0).V ((d.t 0)⁻¹ * g * d.t 0)) = 1 :=
    fun g hg hl PP' hPP' hne => GlobalTheory.T.reduction_eq_one_of_supportedAt_orthogonal_splitPlace D (G ⟨PP', hPP'⟩).k (G ⟨PP', hPP'⟩).q PP' (G ⟨PP', hPP'⟩).idem (G PP).q.e
      (horth PP ⟨PP', hPP'⟩ fun h => hne (congrArg Subtype.val h).symm) _ _ _
      (GlobalTheory.PlaceMatch.suppAt_conj' hg _) (hst _ hl)
  obtain ⟨n, γ, hnN, hnJ, hγJ, hc⟩ := GlobalTheory.T.exists_N_embX_inv_mul_mem_KOne' (G PP).k (G PP).s D.R.k (G PP).S x.1 x.2
  obtain ⟨hup1, hup2⟩ := GlobalTheory.T.levelZeroUniformizerFrame_unipotent_and_embedGL (G PP).k (G PP).s D.R.k (G PP).S (Fin D.R.t)
  obtain ⟨hupN, -⟩ := hup1 ⟨n, hnJ⟩ hnN
  rw [hρ] at hupN
  obtain ⟨ν, hν⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q)
    ((G PP).FY 0 ((G PP).s + 1) (Nat.zero_add _)) (GlobalTheory.LevZeroGen.upZero (G PP).S (Fin D.R.t) n)
  obtain ⟨η, hη⟩ := GlobalTheory.LocMod.Witness.exists_isLoc (GlobalTheory.LocMod.ofSplit (G PP).q) ((G PP).FX 0 (Nat.zero_le _))
    (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin D.R.k) (Fin D.R.t)) γ)
  have hη' := GlobalTheory.T.besselFrame_embedding_localElement_eq_embedded_matrix D (G PP).k _ _ _ _ _ _ _ _ hbes η _ hη
  rw [← hup2] at hη'
  have hνl := hLev ν _ hν ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hnJ)
  have hηl := hLev _ _ hη' ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 hγJ)
  have hQν := hN PP ν _ (GlobalTheory.LocFlag.mem_flagN D _ _ _ _ _ _ _ _ _ hbes ν _ hupN hν) hupN hν hνl
  have hQη := hU η (GlobalTheory.PlaceMatch.mem_GfC_of_suppAt' (G PP).q.split hη.1) hηl
  have hprod := GlobalTheory.LocGrp.isLoc_mul _ hν hη'
  rw [← map_mul] at hprod
  have e : (d.t 0)⁻¹ * ν * d.t 0 * ((d.t 0)⁻¹ * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η * d.t 0) =
      (d.t 0)⁻¹ * (ν * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η) * d.t 0 := by group
  have hl : (d.t 0)⁻¹ * (ν * embA (d.bes 0 D.R.rS h0).d (d.bes 0 D.R.rS h0).o η) * d.t 0 ∈ d.lev 0 :=
    hLev _ _ hprod ((GlobalTheory.LevZeroGen.upZero_mem_lev _ _ _).2 (mul_mem hnJ hγJ))
  refine ⟨_, hl, e ▸ hmul _ hνl _ hηl hQν hQη, fun hr => ?_, hoff _ hprod.1 hl⟩
  exact GlobalTheory.PlaceMatch.red_of_congr (G PP) x ⟨_, mul_mem hnJ hγJ⟩ _
    (GlobalTheory.T.local_level_zero_stabilizer_mem D u d τ PP.1 (G PP) hB hr _ ⟨_, mul_mem hnJ hγJ⟩ hprod (hst _ hl)) hc
end
end
