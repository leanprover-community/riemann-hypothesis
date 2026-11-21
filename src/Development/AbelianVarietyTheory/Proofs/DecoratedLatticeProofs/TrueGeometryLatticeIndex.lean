import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsMatrixInFrameOfXZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryLastRowCongrOneMemLocalLevelLevelPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PulledLatticeVectorMemDualBaseLatticeCompletion
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryFinalCharacterStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E}, J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (p q : 𝓞 E), (q : E) = σ (p : E) → (p : E) * (q : E) = (T : E) → IsCoprime p q → T ≠ 0 → S.Lb = Formalism.L2.Col.rll_dLat n ((p : E)⁻¹) → ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ Formalism.UG.UPts σ J (v.adicCompletion F) → (∀ r s, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) r s ∈ Formalism.BasicNotions.intV E v) → (∀ s, ∃ c ∈ Formalism.BasicNotions.intV E v, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s - (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) (Formalism.L2.Col.lastIdx n) s = Formalism.UG.inclE (F := F) (v.adicCompletion F) (p : E) * c) → x ∈ S.Uloc v := by
  first | exact @GlobalTheory.UnitLocLastRow.mem_Uloc | exact GlobalTheory.UnitLocLastRow.mem_Uloc | (intros; apply GlobalTheory.UnitLocLastRow.mem_Uloc <;> assumption)
end

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MovesEntries

theorem map_mulVec_single {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (y : Fin n → A) (r s : Fin n) (h1 : f (y s) = 1)
    (h0 : ∀ b, b ≠ s → y b = 0) : f ((M *ᵥ y) r) = f (M r s) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [Finset.sum_eq_single s]
  · rw [h1, mul_one]
  · intro b _ hb
    rw [h0 b hb, map_zero, mul_zero]
  · intro hs
    exact (hs (Finset.mem_univ _)).elim

theorem toEAf_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = e ⊗ₜ[D.host.F] α := by
  rfl

theorem infPart_pair (D : D7) (α : Af D.host.F) (e : D.host.E) :
    infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e) = 0 := by
  have : infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] e)
      = (0 : Ainf D.host.F) ⊗ₜ[D.host.F] e := rfl
  rw [this, TensorProduct.zero_tmul]

theorem coord_int (D : D7) (S : HSp D) (L : GlobalTheory.FinPl.Lat S)
    (hL : ∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) (v : HeightOneSpectrum (𝓞 D.host.F))
    (y : Fin S.rank → AE D) (hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True)) (i : Fin S.rank) :
    Formalism.UG.prV (E := D.host.E) v (toEAf D (y i)) ∈ Formalism.BasicNotions.intV D.host.E v := by
  unfold GlobalTheory.FinPl.latV GlobalTheory.FinPl.latMul at hy
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, -, a, ha, x, hx, rfl⟩ := hy
    rw [Set.mem_singleton_iff] at ha
    subst ha
    have hxi : IsIntegral ℤ (x i) := (hL x).1 hx i
    have h1 : Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i)))
        = ((x i) ⊗ₜ[D.host.F] (1 : v.adicCompletion D.host.F))
          * ((1 : D.host.E) ⊗ₜ[D.host.F] (evalV D.host.F v α : v.adicCompletion D.host.F)) := by
      rw [toEAf_pair, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
      rfl
    show Formalism.UG.prV (E := D.host.E) v
        (toEAf D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 * x i))) ∈ _
    rw [h1]
    refine Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨⟨x i, ⟨⟨x i, hxi⟩, rfl⟩⟩, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨⟨evalV D.host.F v α, hα v⟩, rfl⟩))
  | zero =>
    rw [Pi.zero_apply, (toEAf D).map_zero, (Formalism.UG.prV (E := D.host.E) v).map_zero]
    exact Subring.zero_mem _
  | add a b _ _ ha hb =>
    rw [Pi.add_apply, (toEAf D).map_add, (Formalism.UG.prV (E := D.host.E) v).map_add]
    exact Subring.add_mem _ ha hb
  | neg a _ ha =>
    rw [Pi.neg_apply, (toEAf D).map_neg, (Formalism.UG.prV (E := D.host.E) v).map_neg]
    exact Subring.neg_mem _ ha

theorem finM_entry_int : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  intro D S n hn L hL κ hκ v r s
  subst hn
  let x : Fin S.rank → D.host.E := Pi.single s 1
  have hx : x ∈ L := by
    rw [hL]
    intro k
    by_cases hk : k = s
    · subst hk
      simp only [x, Pi.single_eq_same]
      exact isIntegral_one
    · simp only [x, Pi.single_eq_of_ne hk]
      exact isIntegral_zero
  let y : Fin S.rank → AE D := fun i => pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 * x i)
  have hy : y ∈ GlobalTheory.FinPl.latV S L (fun _ => True) := by
    refine AddSubgroup.subset_closure ⟨1, ?_, fun w hw => (hw trivial).elim, 1, rfl, x, hx, rfl⟩
    intro w
    rw [map_one]
    exact one_mem _
  have hid : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) := by
    intro i
    refine Submodule.mem_inf.2 ⟨infPart_pair D _ _, ?_⟩
    rw [Submodule.mem_iInf]
    intro w
    exact (w.2 trivial).elim
  have h := coord_int D S L hL v _ ((hκ y hid).1 hy) r
  have h2 : toEAf D ((Formalism.L2.Theta.mt S κ *ᵥ y) r) = toEAf D (Formalism.L2.Theta.mt S κ r s) := by
    refine map_mulVec_single (toEAf D) _ y r s ?_ ?_
    · simp only [y, x, toEAf_pair, Pi.single_eq_same, one_mul]
      rfl
    · intro b hb
      simp only [y, x, Pi.single_eq_of_ne hb, mul_zero, TensorProduct.tmul_zero]
  rw [h2] at h
  exact h

end GlobalTheory.FinPl.MovesEntries
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice : ∀ (D : D7) (S : HSp D) {n : ℕ} (hn : S.rank = n) (L : GlobalTheory.FinPl.Lat S), (∀ z, z ∈ L ↔ z ∈ GlobalTheory.AdForm.intVec D S.rank) → ∀ κ : GA D S, GlobalTheory.FinPl.Moves S κ L L (fun _ => True) → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (r s : Fin n), Formalism.UG.prV (E := D.host.E) v (GlobalTheory.AdForm.finM S hn κ r s) ∈ Formalism.BasicNotions.intV D.host.E v := by
  atlas_forward_decl GlobalTheory.FinPl.MovesEntries.finM_entry_int
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem GlobalTheory.FamTrace.uloc_T_of_inLevG : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FamTrace.InLevG a κ → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), (((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal) → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ (F0 W u).cls0.lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha hat row col hc κ hκ y hy hIn v hv
  have hF := hA.tr.std.some u
  have hI := hA.tr.ok
  have hP := hA.tr.pins.some
  obtain ⟨kk, R⟩ := hF.ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hgram : Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _) = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 (Nat.zero_le _)).1
  have hlb := R.lb ()
  haveI : NeZero ((I.rec7 l Z).R.N 0) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s (W.R.T.cols.forms u).atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact (W.R.T.cols.forms u).atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : (((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : (F0 W u).cls0.lev.Lb = Formalism.L2.Col.rll_dLat ((I.rec7 l Z).R.N 0) ((((W.R.T.cols.forms u).atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ (W.R.T.cols.forms u).atT.piU hp0 _ ?_
    rw [hF.piU]; exact hlb
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hcop : IsCoprime (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) := by
    have h1 := hPr.piT_cop u
    have e : s (W.R.T.cols.forms u).atT.piU = B.fields.conjO ((B.primes X).piT u) := by
      apply RingOfIntegers.ext (K := (I.rec7 l Z).host.E)
      rw [hsc, hF.piU]
      exact (B.fields_conjO_coe _).symm
    rw [e, hF.piU]
    exact h1
  have hint : ∀ (w : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (r t : Fin ((I.rec7 l Z).R.N 0)), Formalism.UG.prV (E := (I.rec7 l Z).host.E) w (GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ r t) ∈ Formalism.BasicNotions.intV (I.rec7 l Z).host.E w :=
    GlobalTheory.T.finiteMatrix_entry_integral_of_keeps_standardLattice (I.rec7 l Z) ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) (a.g.x 0).L
      ((hat.std.2 0 (Nat.zero_le _)).1) κ hIn.1
  refine GlobalTheory.T.unitary_lastRow_congr_one_mem_localLevel_levelPrime (Formalism.L2.Forms.sigD (I.rec7 l Z)) (fun x => star_star x) hgram (F0 W u).cls0.lev (W.R.T.cols.forms u).atT.piU (s (W.R.T.cols.forms u).atT.piU) rfl hpq hcop hTp.ne_zero hL v hv _ (GlobalTheory.MemDual.bc_prV_mem_UPts _ _ v y.2) ?_ ?_
  · intro r t
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 r t) ∈ _
    rw [← hy]
    exact hint v r t
  · intro t
    obtain ⟨c, hc, he⟩ := GlobalTheory.T.true_geometry_character W hA u a ha hat κ hκ hIn.2.1 hint v hv t
    refine ⟨c, hc, ?_⟩
    change Formalism.UG.prV (E := (I.rec7 l Z).host.E) v (y.1.1 _ t) - _ = _
    rw [← hy, he, hF.piU]
    rfl

end
end
