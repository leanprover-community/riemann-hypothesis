import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RdLevOn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelReadingRationalAtTwistExtendsIntegralUnitar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter

section
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

noncomputable section

namespace GlobalTheory.SeeSaw.TwLev

theorem lev_iffQ : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E},
    J' = 1 → J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad),
    S.Lb = Formalism.L2.Col.stdLat E n → ∀ {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n'), 0 < t → n = r + s * t →
    ∀ {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    RdLevOn hc Set.univ S.U S.chi (parFam h t s P χ) emb Q (fun _ => blockTri (blk2 r))
      (fun P => (ξ P.1).comp (blkDet (blk2 r) 1)) →
    ∀ (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    (∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H) →
    (∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K)) →
    (∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K)) →
    ∀ (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    (∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) →
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  intro F E K _ _ _ _ _ _ _ hc n n' e _ J' J hJ' hJ T f bad S hL r t s h h' ht hn SG Q P χ emb ξ hR P' cg hH hchi hcg g y hgy
  classical
  subst e hJ' hJ
  obtain rfl : g = y := Units.ext (Matrix.ext hgy)
  have hred : ∀ (hz : g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F))) (w : Pl E), redFn 1 w g = redAt 1 w ⟨g, hz⟩ :=
    fun hz w => extendOne_of_mem _ hz
  have hU : g ∈ S.U → g ∈ UAd hc n' ∧ g ∈ St (1 : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) := fun hy => by
    obtain ⟨h1, h2⟩ := (S.U_eq g).1 hy
    refine ⟨h1, rll_St_of_loc n' g fun v => ⟨_, rll_put_mem_St n' v ?_, rll_put_self n' v _⟩⟩
    have := (S.Uloc_lev v (h2 v)).2
    rw [hL] at this
    exact this
  have e0 : g ∈ lev hc 1 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔
      g ∈ lev hc 1 1 (parDat h t s P χ) ∧ ∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r) := by
    rw [mem_lev, mem_lev, mem_parLev, mem_parLev]
    constructor
    · rintro ⟨⟨a1, a2, a3, a4⟩, a5⟩
      exact ⟨⟨⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty PP)⟩, fun w _ => (hH _).1 a5 w⟩, a4⟩
    · rintro ⟨⟨⟨a1, a2, a3, -⟩, a5⟩, a4⟩
      exact ⟨⟨a1, a2, a3, a4⟩, (hH _).2 fun w => a5 w (Set.mem_univ w)⟩
  have e1 : g ∈ levU hc n' ∅ SG (parFam h t s P χ).grp ∧ (∀ PP ∈ Q, redFn 1 PP g ∈ blockTri (blk2 r)) ↔ g ∈ S.U := by
    rw [mem_levU_iff]
    constructor
    · rintro ⟨⟨h1, h2, -, h4⟩, hq⟩
      exact (hR g (Set.mem_univ g) h2 h1).1.2 ⟨fun w => hred h2 w.1 ▸ h4 w (Set.mem_univ w), fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2⟩
    · intro hy
      obtain ⟨h1, h2⟩ := hU hy
      obtain ⟨a, b⟩ := (hR g (Set.mem_univ g) h2 h1).1.1 hy
      refine ⟨⟨h1, h2, fun P hP => absurd hP (Finset.notMem_empty P), fun w _ => ?_⟩, fun PP hP => ?_⟩
      · have := a w
        rwa [← hred h2] at this
      · have := b ⟨PP, hP⟩
        rwa [← hred h2] at this
  refine ⟨by rw [e0, ← levU_parFam_eq_lev hc h ht hn, e1], fun hy => ?_⟩
  obtain ⟨h1, h2⟩ := hU hy
  obtain ⟨h3, hq⟩ := e1.2 hy
  have h4 : g ∈ lev hc 1 1 (parDat h t s P χ) := levU_parFam_eq_lev hc h ht hn P χ ▸ h3
  have h5 := e0.2 ⟨h4, hq⟩
  obtain ⟨r1, r2⟩ := hR g (Set.mem_univ g) h2 h1
  have hq' : ∀ PP : Q, redAt 1 PP.1 ⟨g, h2⟩ ∈ blockTri (blk2 r) := fun PP => hred h2 PP.1 ▸ hq PP.1 PP.2
  have hw' : ∀ w : SG, redAt 1 w.1 ⟨g, h2⟩ ∈ (parFam h t s P χ w).H := (r1.1 hy).1
  have a1 : ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) =
      emb ((levFn 1 (parDat h t s P χ) g : Kˣ) : K) *
        ∏ PP ∈ Q, ((((ξ PP)⁻¹ (dBlk (blk2 r) 1 (redFn 1 PP g))) : ℂˣ) : ℂ) := by
    have eQ : (parDat h t s P χ).Q = ∅ := rfl
    unfold levFn
    rw [extendOne_of_mem _ h5.2, extendOne_of_mem _ h4.2, eQ, Finset.prod_empty, mul_one]
    simp only [Units.val_mul, Units.coe_prod, map_mul, map_prod]
    congr 1
    congr 1
    · rw [hchi _ fun w => h4.2 w (Set.mem_univ w)]
      have := rld_ofLocal_chi (fun w => (P w).H) (fun w => (P w).lam) ⟨_, h4.2⟩
      refine Eq.trans ?_ (congrArg (fun x : Kˣ => emb (x : K)) this).symm
      simp only [Units.coe_prod, map_prod]
      rfl
    · show ∏ PP ∈ SG, _ = ∏ PP ∈ SG, _
      refine Finset.prod_congr rfl fun w hw => ?_
      show ∏ c ∈ Finset.range s, _ = ∏ c ∈ Finset.range s, _
      refine Finset.prod_congr rfl fun c _ => ?_
      rw [rld_parDat_cg h P χ c ⟨w, hw⟩]
      exact hcg c ⟨w, hw⟩ _
  have a2 := levChr_parFam_eq_levChar hc h ht hn P χ g h3 h4
  rw [levChar_apply] at a2
  rw [a1, ← a2, r2 hy hw' hq', star_mul']
  congr 1
  · show emb ((piChar (fun w => (parFam h t s P χ w).H) (fun w => (parFam h t s P χ w).lam) (levRed hc n' ∅ SG _ ⟨g, h3⟩) : Kˣ) : K) = _
    rw [piChar_apply, Units.coe_prod, map_prod, star_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    have : Finite (𝓞 E ⧸ w.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
    have b1 := ((emb.toMonoidHom.comp ((Units.coeHom K).comp (parFam h t s P χ w).lam)).isOfFinOrder
      (isOfFinOrder_of_finite ⟨_, hw' w⟩)).norm_eq_one
    refine Eq.trans ?_ ((congrArg star (Complex.inv_eq_conj b1)).trans (Complex.conj_conj _)).symm
    exact congrArg (fun x => emb (((parFam h t s P χ w).lam x : Kˣ) : K))
      (Subtype.ext ((levRed_apply hc n' ∅ SG _ ⟨g, h3⟩ w).trans (hred h2 w.1)))
  · rw [star_prod, ← Finset.prod_coe_sort Q]
    refine Finset.prod_congr rfl fun PP _ => ?_
    have : Finite (𝓞 E ⧸ PP.1.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    have ed : dBlk (blk2 r) 1 (redFn 1 PP.1 g) = blkDet (blk2 r) 1 ⟨_, hq' PP⟩ := by
      unfold dBlk
      rw [extendOne_of_mem _ (hq PP.1 PP.2)]
      exact congrArg _ (Subtype.ext (hred h2 PP.1))
    rw [ed, MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
    have b1 := (((Units.coeHom ℂ).comp (ξ PP.1)).isOfFinOrder
      (isOfFinOrder_of_finite (blkDet (blk2 r) 1 ⟨_, hq' PP⟩))).norm_eq_one
    exact Complex.inv_eq_conj b1

end GlobalTheory.SeeSaw.TwLev

end
end

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPrimeLevel_iff_reductionLevel_conjugateCharacter : ∀ {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K]
    (hc : CMData F E) {n n' : ℕ} (e : n' = n) [NeZero n] {J' : Matrix (Fin n') (Fin n') E} {J : Matrix (Fin n) (Fin n) E},
    J' = 1 → J = 1 → ∀ {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad),
    S.Lb = Formalism.L2.Col.stdLat E n → ∀ {r t s : ℕ} (h : r ≤ n) (h' : r ≤ n'), 0 < t → n = r + s * t →
    ∀ {SG Q : Finset (Pl E)} (P : LevFam E K r SG) (χ : ∀ w : SG, ℕ → (𝓞 E ⧸ w.1.asIdeal)ˣ →* Kˣ) (emb : K →+* ℂ)
    (ξ : ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    RdLevOn hc Set.univ S.U S.chi (parFam h t s P χ) emb Q (fun _ => blockTri (blk2 r))
      (fun P => (ξ P.1).comp (blkDet (blk2 r) 1)) →
    ∀ (P' : LevelP SG r ℂ) (cg : ℕ → ∀ PP : Pl E, (kP PP)ˣ →* ℂˣ),
    (∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (P w).H) →
    (∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (P w).H), ((P'.chi g : ℂˣ) : ℂ) = ∏ w, emb (((P w).lam ⟨g.1 w, hg w⟩ : Kˣ) : K)) →
    (∀ c (w : SG) a, ((cg (c + 1) w.1 a : ℂˣ) : ℂ) = emb ((χ w c a : Kˣ) : K)) →
    ∀ (g : GL (Fin n') (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)),
    (∀ i j, g.1 i j = y.1 (finCongr e i) (finCongr e j)) →
    (g ∈ lev hc J' 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ ↔ y ∈ S.U) ∧
      ∀ hy : y ∈ S.U, ((levFn 1 ⟨r, h', t, s, SG, Q, P', cg, fun PP => (ξ PP)⁻¹⟩ g : ℂˣ) : ℂ) = star ((S.chi ⟨y, hy⟩ : ℂˣ) : ℂ) := by
  atlas_forward_decl GlobalTheory.SeeSaw.TwLev.lev_iffQ
end

section
noncomputable section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.SeeSaw.TopLevel

namespace GlobalTheory.SeeSaw.TwLev

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem cl_nonempty {B : Base} {X : PreX B.toPre} (I : TC B X) (a : I.ι) : Nonempty (I.stX a).Cl := by
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  exact ⟨⟨(), Quotient.mk _ ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩⟩

theorem q_inj {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (a : I.ι) :
    ∀ P P' : I.Q a, underPl B.host.F P.1 = underPl B.host.F P'.1 → P = P' := by
  classical
  intro P P' e
  rcases (GlobalTheory.Mem.Col2.under_eq_iff B.host P.1 P'.1).1 (HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal e.symm)) with h | h
  · exact Subtype.ext h.symm
  · exact absurd (h ▸ Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P'.2))
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).1.split P.1 (Finset.mem_union_right _ (GlobalTheory.Mem.Col2.ChEx.q_sub_SQ I a P.2)))

set_option maxHeartbeats 2000000 in

theorem levIs_reads_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (a : I.ι) (ha : a ≠ I.mu0) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}
    (hO : letI := Formalism.BasicNotions.tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F);
      ∀ᶠ (u : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) in nhds 1,
        ∀ κ : S.U, κ.1 = u → S.chi κ = 1)
    (hK : I.ReadsP a S.Lb S.U S.chi y lat st)
    (P' : LevelP (B.primes X).vGs B.R.r ℂ) (hH : ∀ g, g ∈ P'.H ↔ ∀ w, g w ∈ (I.Ps w).H)
    (hchi : ∀ (g : P'.H) (hg : ∀ w, g.1 w ∈ (I.Ps w).H),
      ((P'.chi g : ℂˣ) : ℂ) = ∏ w, B.embLL (((I.Ps w).lam ⟨g.1 w, hg w⟩ : B.LLˣ) : B.LL))
    (cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hcg : ∀ c (w : (B.primes X).vGs) x, ((cg (c + 1) w.1 x : ℂˣ) : ℂ) = B.embLL ((Formalism.L2.Col.chiAt I.Ch w c x : B.LLˣ) : B.LL))
    (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ)
    (hξ : ∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL))
    (hr : B.R.r ≤ (I.rec7 l Z).sp.X'.rank),
    LevIs S (levS _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B))
      (Lev.levChi _ 1 (Lev.datY (I.rec7 l Z).sp.X'.rank B.R.r B.R.t B.R.m hr (B.primes X).vGs (I.Q a) P' cg ξ Lev.Frm.B)) := by
  intro B X I hOk hPins l Z a ha bad S y lat st hO hK P' hH hchi cg hcg ξ hξ hr
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have gX : (I.rec7 l Z).sp.X'.gram = 1 := by
    have := congrArg (Matrix.reindex (finCongr (rankP (I.rec7 l Z))) (finCongr (rankP (I.rec7 l Z)))).symm gP
    rw [gramP, Equiv.symm_apply_apply] at this
    rw [this, Matrix.reindex_symm, Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  have hLb : S.Lb = Formalism.L2.Col.stdLat B.fields.E (B.R.N B.R.m - 1) := by
    ext x
    refine (hK.lb x).trans (Iff.trans ?_ (Formalism.L2.Col.mem_stdLat x).symm)
    exact forall_congr' fun j => ⟨fun ⟨r, h, _⟩ => ⟨r, h.symm⟩, fun ⟨r, h⟩ => ⟨r, h.symm, fun _ => one_dvd _⟩⟩
  obtain ⟨c⟩ := cl_nonempty I a
  have hR := GlobalTheory.T.levelReading_rationalAtTwist_extends_integralUnitary (Q := I.Q a) B.sp.cm gP S (rowTyG I.Ch I.Ps) B.embLL _ _ (GlobalTheory.Mem.Col2.ChEx.q_conj I hOk a)
    (q_inj I hOk a) hO (GlobalTheory.T.twistedTuple_reading_level_character I hOk hPins l Z a S hK c ξ hξ)
  have key := @GlobalTheory.T.twistPrimeLevel_iff_reductionLevel_conjugateCharacter B.fields.F B.fields.E B.fields.K _ _ _ _ (GlobalTheory.Mem.Col2.starE B) _ _ B.sp.cm (B.R.N B.R.m - 1) _
    (rankP (I.rec7 l Z)) _ _ _ gX gP _ _ _ S hLb B.R.r B.R.t B.R.m (Formalism.L2.Col.r_le_X' B.R) hr
    (Formalism.L2.Col.t_pos B.R) (Formalism.L2.Col.rank_X'_eq B.R) (B.primes X).vGs (I.Q a) I.Ps (Formalism.L2.Col.chiAt I.Ch) B.embLL ξ hR
    P' cg hH hchi hcg
  show (∀ h, h ∈ levS _ 1 _ ↔ _) ∧ _
  refine ⟨fun h => ⟨fun hh => ?_, fun ⟨κ, h1, h2⟩ => ⟨h1, (key _ κ.1 h2).1.2 κ.2⟩⟩, fun h κ hκ => (key _ κ.1 hκ.2).2 κ.2⟩
  obtain ⟨y, hy⟩ := exists_copy (rankP (I.rec7 l Z)) (Lev.finE (I.rec7 l Z).sp.X' h)
  exact ⟨⟨y, (key _ y hy).1.1 hh.2⟩, hh.1, hy⟩

end GlobalTheory.SeeSaw.TwLev
end
end
