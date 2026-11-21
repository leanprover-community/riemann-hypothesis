import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PinColL
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTuple
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StpTopIdxEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopLevExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMMulVecFix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMulStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoordsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LastAllTranspose
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastGroupEmbeddingRealComponentsBlockForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp

section
noncomputable section

namespace GlobalTheory.AdForm.LevChiTop

section Mat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open GlobalTheory.Mem.Col2.TilX
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

def Deep {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (N : ℕ) (w : GL (Fin n) (AfE F E)) : Prop :=
  (∀ P', P' ≠ P → P' ≠ conjPrime₂ P → ∀ i j, adAt F P' (w.1 i j) = if i = j then 1 else 0) ∧
    ∀ r s, Valued.v (adAt F P (w.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ))

theorem Deep.mono {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (h : N ≤ N') {w : GL (Fin n) (AfE F E)} (hw : Deep P N' w) :
    Deep P N w :=
  ⟨hw.1, fun r s => (hw.2 r s).trans (WithZero.exp_le_exp.2 (by omega))⟩

theorem Deep.ext {n M : ℕ} (hM : M = n + 1) {P : HeightOneSpectrum (𝓞 E)} {N : ℕ} {w : GL (Fin n) (AfE F E)} (hw : Deep P N w) :
    Deep P N (extGL hM w) := by
  subst hM
  refine ⟨fun P' h1 h2 a b => ?_, fun a b => ?_⟩
  · rw [extGL_val]
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [extM_last_last]
    · rw [extM_last_castSucc, if_neg (Fin.castSucc_lt_last j).ne', map_zero]
    · rw [extM_castSucc_last, if_neg (Fin.castSucc_lt_last i).ne, map_zero]
    · rw [extM_castSucc, hw.1 P' h1 h2]
      simp [Fin.castSucc_inj]
  · rw [extGL_val]
    refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
    · simp [extM_last_last]
    · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
      simp
    · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
      simp
    · have := hw.2 i j
      rw [extM_castSucc]
      simpa [Matrix.one_apply, Fin.castSucc_inj] using this

theorem exists_deep (hc : CMData F E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E hc.sig J T f bad) (P : HeightOneSpectrum (𝓞 E))
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    (hu : (conjPrime₂ P).under (𝓞 F) = P.under (𝓞 F)) :
    ∃ N : ℕ, ∀ w ∈ UAd hc n, Deep P N w → w ∈ S.U := by
  obtain ⟨N, hN⟩ := Opn.exists_depth_step hc hJ S P (P.under (𝓞 F)) rfl
  subst hJ
  refine ⟨N, fun w hw hd => hN w hw (fun v' hv' => ?_) fun r s => (AdelicValuationDictionary.entry_iff P hq N w r s).2 (hd.2 r s)⟩
  refine AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' w fun P' hP' => hd.1 P' (fun e => hv' ?_) fun e => hv' ?_
  · rw [← hP', e]
  · rw [← hP', e, hu]

theorem exists_rat (hc : CMData F E) {n m : ℕ} (hm : 0 < m) (Q : Finset (HeightOneSpectrum (𝓞 E))) (hQ : ∀ P ∈ Q, conjPrime₂ P ∉ Q)
    (H : Subgroup (GL (Fin n) (AfE F E))) (hH : ∀ P ∈ Q, ∃ N : ℕ, ∀ w ∈ UAd hc n, Deep P N w → w ^ m ∈ H)
    (g : GL (Fin n) (AfE F E)) :
    ∃ z ∈ H, ∀ P ∈ Q, ∃ γ : GL (Fin n) E, ∀ r s, adAt F P ((g * z).1 r s) = algebraMap E (P.adicCompletion E) (γ.1 r s) := by
  classical
  suffices h : ∀ S : Finset (HeightOneSpectrum (𝓞 E)), S ⊆ Q → ∃ z ∈ H, ∀ P ∈ S, ∃ γ : GL (Fin n) E,
      Matrix.GeneralLinearGroup.map (adAt F P) (g * z) = Matrix.GeneralLinearGroup.map (algebraMap E (P.adicCompletion E)) γ by
    obtain ⟨z, hz, h⟩ := h Q subset_rfl
    refine ⟨z, hz, fun P hP => ?_⟩
    obtain ⟨γ, hγ⟩ := h P hP
    exact ⟨γ, fun r s => congrArg (fun x : GL (Fin n) (P.adicCompletion E) => x.1 r s) hγ⟩
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => ⟨1, H.one_mem, fun P hP => absurd hP (Finset.notMem_empty _)⟩
  | insert P S hPS ih =>
    intro hS
    obtain ⟨z, hz, hzS⟩ := ih ((Finset.subset_insert _ _).trans hS)
    have hPQ : P ∈ Q := hS (Finset.mem_insert_self _ _)
    obtain ⟨N, hN⟩ := hH P hPQ
    obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
    obtain ⟨M, γ, hM1, -, hM3⟩ := OnePrime.exists_root_rat E P n m N hm (algebraMap E _ π) ((AdelicValuationDictionary.vAlg P π).trans hπ)
      (Matrix.GeneralLinearGroup.map (adAt F P) (g * z)) 1
    have hne : conjPrime₂ P ≠ P := fun e => hQ P hPQ (by rw [e]; exact hPQ)
    obtain ⟨w, hw, hw1, hw2⟩ := AdLift.exists_unitary hc hne M
    have hd : Deep P N w := ⟨hw1, fun r s => by rw [hw2]; exact hM1 r s⟩
    refine ⟨z * w ^ m, H.mul_mem hz (hN w hw hd), fun P' hP' => ?_⟩
    rw [← mul_assoc, map_mul, map_pow]
    rcases Finset.mem_insert.1 hP' with rfl | hP'S
    · have e : Matrix.GeneralLinearGroup.map (adAt F P') w = M := Units.ext (Matrix.ext hw2)
      rw [e]
      exact ⟨γ, (mul_one _).symm.trans hM3⟩
    · have e : Matrix.GeneralLinearGroup.map (adAt F P') w = 1 := Units.ext (Matrix.ext fun i j => by
        rw [Units.val_one, Matrix.one_apply]
        exact hw1 P' (fun e => hPS (e ▸ hP'S)) (fun e => hQ P hPQ (e ▸ hS (Finset.mem_insert_of_mem hP'S))) i j)
      rw [e, one_pow, mul_one]
      exact hzS P' hP'S

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1600000 in

theorem exists_ka (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k) (c : (I.stp u a B.R.m).Cl) (g : GA B (B.R.N B.R.m))
    (m : (I.stp u a B.R.m).G c.1)
    (hp : PtOf (g * k (chOf c)) ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1) :
    ∃ κ : U (chOf c),
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam _ m) * y c = g * κ.1 ∧
      (((chi _ κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr _ m : B.LLˣ) : B.LL) := by
  have hp' : PtOf (ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c))) _ :=
    isPtOf_rat hp (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹
  let κ0 : (I.stp u a B.R.m).G c.1 := (1, m.2.1, m.2.2)
  have hgam : (I.stp u a B.R.m).gam c.1 κ0 = 1 := map_one (ufGL B.fields.E (B.R.N B.R.m))
  have hact : ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1 =
      (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) •
        ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1 := by
    have e1 : FrmG.incl _ _ m • ((I.stp u a B.R.m).rep c).1.1 = ((I.stp u a B.R.m).act c.1 m ((I.stp u a B.R.m).rep c)).1.1 := rfl
    rw [← e1]
    refine Eq.trans ?_ (smul_smul _ _ _).symm
    have e2 : FrmG.incl (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1)
        (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m c.1) κ0 =
        (((m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹, 1, 1) :
        UF B.fields.E (B.R.N B.R.m) × GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × GLQ B.fields.E (B.R.N B.R.m) (I.Q a)) *
        FrmG.incl _ _ m := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · exact (inv_mul_cancel _).symm
      · exact (one_mul _).symm
      · exact (one_mul _).symm
    exact congrArg (fun t => t • ((I.stp u a B.R.m).rep c).1.1) e2
  have hcos : cosetIn ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)) = cosetIn ((I.stp u a B.R.m).rep c) :=
    GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (by omega) _ _
  obtain ⟨x, hx⟩ : ∃ x : GA B (B.R.N B.R.m), x = (y c)⁻¹ * ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * g := ⟨_, rfl⟩
  have hxk : y c * x * k (chOf c) = ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ * (g * k (chOf c)) := by
    rw [hx]; group
  have hq : PtOf (y c * x * k (chOf c)) ((I.stp u a B.R.m).act c.1 κ0 ((I.stp u a B.R.m).rep c)).1.1 := by
    rw [hxk, hact]
    exact hp'
  have hxU : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ0, hgam, rfl, hcos⟩
  have hchr := hR.chr c ⟨x, hxU⟩ κ0 hgam hq
  refine ⟨⟨x, hxU⟩⁻¹, ?_, ?_⟩
  · have e : ratAd B.host.F (m.1 : UF B.fields.E (B.R.N B.R.m))⁻¹ =
        (bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a B.R.m).gam c.1 m))⁻¹ := by
      unfold ratAd
      rw [map_inv, map_inv]
      rfl
    show _ = g * x⁻¹
    rw [hx, e]
    group
  · rw [map_inv, inv_inv]
    exact hchr

set_option maxHeartbeats 3200000 in

theorem ext_mem_of_pt (l : I.Laws) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)), PtOf g' d →
      PtOf (extGL (N_m_succ B.R) g' * k β) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d))
    {Lb' U' chi' y' lat' st'} (hK : I.ReadsP a Lb' U' chi' y' lat' st') (c : (I.stX a).Cl) (x : U')
    (q : XPt (B.primes X) B.R I.sel (I.tup a)) (hq : PtOf (y' c * x.1) q) :
    ∃ h : extGL (N_m_succ B.R) x.1 ∈ U (chOf ((I.perIn u a).tilC c)), chi _ ⟨_, h⟩ = chi' x := by
  obtain ⟨κ', hg, hact⟩ := (hK.lev c x.1 q hq).1 x.2
  have hchr := hK.chr c x κ' hg (hact ▸ hq)
  have hm := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  obtain ⟨m, hmm⟩ : ∃ m, m = (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) := ⟨_, rfl⟩
  rw [← hmm] at hm
  have hm1 : ((I.stp u a B.R.m).act (I.perIn u a).b0 m ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u ((I.stX a).rep c).1.1 :=
    congrArg (fun d : (I.stp u a B.R.m).D (I.perIn u a).b0 => d.1.1) hm
  have hts := (l.per u a).til_smul c.1 κ' ((I.stX a).rep c)
  have hm2' : (I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)) =
      (I.perIn u a).til c.1 ((I.stX a).act c.1 κ' ((I.stX a).rep c)) := by
    refine Eq.trans ?_ hts.symm
    refine (@mul_smul _ _ _ ((I.stp u a B.R.m).actD (I.perIn u a).b0).toSemigroupAction _ _ _).trans ?_
    exact congrArg ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ')) hm
  have hm2 : ((I.stp u a B.R.m).act (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 =
      tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u q := by
    rw [hm2', ← hact]
    rfl
  obtain ⟨κ₁, e₁, c₁⟩ := exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c)) m
    (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ (hK.pt c); rw [← hm1] at h; exact h)
  obtain ⟨κ₂, e₂, c₂⟩ := exists_ka I u a hR ((I.perIn u a).tilC c) (extGL (N_m_succ B.R) (y' c * x.1)) ((I.perIn u a).ext c.1 κ' * m)
    (by have h := hT (chOf ((I.perIn u a).tilC c)) _ _ hq; rw [← hm2] at h; exact h)
  have hg1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ') = 1 := by
    have h1 := TwP.eq_extM_of_laws (N_m_succ B.R) _ _ (fun z => (l.per u a).gam_ini c.1 κ' z) (fun z => (l.per u a).gam_last c.1 κ' z)
    have h2 : ((I.perIn u a).S'.gam c.1 κ').1 = 1 := congrArg Units.val hg
    rw [h2, extM_one] at h1
    exact Units.ext h1
  have hg2 : (I.stp u a B.R.m).gam (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) = (I.stp u a B.R.m).gam (I.perIn u a).b0 m := by
    rw [map_mul, hg1, one_mul]
  have e₃ : extGL (N_m_succ B.R) (y' c) * κ₁.1 = extGL (N_m_succ B.R) (y' c * x.1) * κ₂.1 :=
    e₁.symm.trans ((congrArg (fun t => bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) t *
      y ((I.perIn u a).tilC c)) hg2).symm.trans e₂)
  have e₄ : extGL (N_m_succ B.R) x.1 = (κ₁ * κ₂⁻¹).1 := by
    rw [map_mul, mul_assoc] at e₃
    show _ = κ₁.1 * κ₂.1⁻¹
    rw [mul_left_cancel e₃, mul_inv_cancel_right]
  have c₃ : (I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.perIn u a).ext c.1 κ' * m) =
      (I.stX a).chr c.1 κ' * (I.stp u a B.R.m).chr (I.perIn u a).b0 m := by
    rw [map_mul]
    exact congrArg (· * (I.stp u a B.R.m).chr (I.perIn u a).b0 m) ((l.per u a).chr_ext c.1 κ')
  have c₄ : (chi _ κ₂)⁻¹ = chi' x * (chi _ κ₁)⁻¹ := by
    refine Units.ext ?_
    rw [Units.val_mul, c₁, c₂, hchr, ← map_mul, ← Units.val_mul]
    exact congrArg (fun t : B.LLˣ => B.embLL (t : B.LL)) c₃
  refine ⟨e₄ ▸ (κ₁ * κ₂⁻¹).2, ?_⟩
  have e₅ : (⟨extGL (N_m_succ B.R) x.1, e₄ ▸ (κ₁ * κ₂⁻¹).2⟩ : U (chOf ((I.perIn u a).tilC c))) = κ₁ * κ₂⁻¹ := Subtype.ext e₄
  rw [e₅, map_mul, map_inv, c₄, mul_comm (chi' x), mul_inv_cancel_left]

theorem mem_sb {a : I.ι} {P : HeightOneSpectrum (𝓞 B.fields.E)} (hP : P ∈ I.Q a) : P ∈ SBof I a := by
  classical
  show P ∈ uSG _ _
  exact Finset.mem_union_right _ hP

set_option maxHeartbeats 3200000 in

theorem ext_mem (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) {Ch : Type} {chOf : (I.stp u a B.R.m).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N B.R.m) → B.host.E)}
    {U : Ch → Subgroup (GA B (B.R.N B.R.m))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a B.R.m).Cl → GA B (B.R.N B.R.m)}
    {st : ∀ c, (I.stp u a B.R.m).Stab c → GL (Fin (B.R.N B.R.m)) B.host.E} {k : Ch → GA B (B.R.N B.R.m)}
    (hR : I.Reads u a B.R.m chOf Lb U chi y st k)
    (hT : ∀ β (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)), PtOf g' d →
      PtOf (extGL (N_m_succ B.R) g' * k β) (tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u d))
    {Lb' U' chi' y' lat' st'} (hK : I.ReadsP a Lb' U' chi' y' lat' st') (β : Ch) (hβ : ∀ c, chOf c = β)
    (hU' : U' ≤ UAd B.sp.cm (B.R.N B.R.m - 1))
    (hd : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m), Deep (F := B.host.F) P N w → w ∈ U β)
    (hd' : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m - 1), Deep (F := B.host.F) P N w → w ∈ U')
    (hn : ∃ n : ℕ, 0 < n ∧ ∀ κ, chi β κ ^ n = 1) (hn' : ∃ n : ℕ, 0 < n ∧ ∀ κ, chi' κ ^ n = 1) (κ : U') :
    ∃ h : extGL (N_m_succ B.R) κ.1 ∈ U β, chi β ⟨_, h⟩ = chi' κ := by
  obtain ⟨n, hn0, hn⟩ := hn
  obtain ⟨n', hn0', hn'⟩ := hn'
  haveI : NeZero (B.R.N B.R.m - 1) := ⟨by
    have := Formalism.L2.Col.rank_X'_eq B.R; have := B.R.m_add_three_le_k; unfold Ranks.r at *; omega⟩
  let c : (I.stX a).Cl := ⟨(), Quotient.mk'' ⟨(DecoF.base _ _ _ _ _, ∅), Set.mem_singleton _⟩⟩
  let H : Subgroup (GA B (B.R.N B.R.m - 1)) :=
    (chi'.ker.map U'.subtype) ⊓ ((chi β).ker.map (U β).subtype).comap (extGL (N_m_succ B.R))
  have hQ : ∀ P ∈ I.Q a, conjPrime₂ P ∉ I.Q a := fun P hP hP' =>
    GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem
      (mem_sb I hP) (mem_sb I hP')
  have hH : ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm (B.R.N B.R.m - 1), Deep (F := B.host.F) P N w → w ^ (n * n') ∈ H := by
    intro P hP
    obtain ⟨N, hN⟩ := hd P hP
    obtain ⟨N', hN'⟩ := hd' P hP
    refine ⟨N + N', fun w hw hw' => ⟨?_, ?_⟩⟩
    · refine ⟨(⟨w, hN' w hw (hw'.mono (by omega))⟩ : U') ^ (n * n'), ?_, rfl⟩
      show chi' _ = 1
      rw [map_pow, mul_comm, pow_mul, hn', one_pow]
    · refine ⟨(⟨extGL (N_m_succ B.R) w, hN _ (extGL_mem_ustd _ hw) ((hw'.mono (by omega)).ext _)⟩ : U β) ^ (n * n'), ?_,
        (map_pow (extGL (N_m_succ B.R)) w (n * n')).symm⟩
      show chi β _ = 1
      rw [map_pow, pow_mul, hn, one_pow]
  obtain ⟨z, ⟨⟨z₁, hz₁, e₁⟩, ⟨z₂, hz₂, e₂⟩⟩, hz⟩ := exists_rat B.sp.cm (Nat.mul_pos hn0 hn0') (I.Q a) hQ H hH (y' c * κ.1)
  have e₁' : z₁.1 = z := e₁
  have e₂' : z₂.1 = extGL (N_m_succ B.R) z := e₂
  have hz₁' : chi' z₁ = 1 := hz₁
  have hz₂' : chi β z₂ = 1 := hz₂
  have hun : y' c * (κ * z₁).1 ∈ UAd B.sp.cm (B.R.N B.R.m - 1) := mul_mem (hK.pt c).uni (hU' (κ * z₁).2)
  have e₃ : y' c * (κ * z₁).1 = y' c * κ.1 * z := by rw [← e₁', mul_assoc]; rfl
  obtain ⟨q, hq⟩ : ∃ q : XPt (B.primes X) B.R I.sel (I.tup a), PtOf (y' c * (κ * z₁).1) q :=
    RatFrPt.exists_isPtOf_of_rat B.sp.cm _ _ _ _ hun (by rw [e₃]; exact hz)
  have key := ext_mem_of_pt I l u a hR hT hK c (κ * z₁) q hq
  rw [hβ] at key
  obtain ⟨h, hc⟩ := key
  have e₄ : extGL (N_m_succ B.R) κ.1 = ((⟨_, h⟩ : U β) * z₂⁻¹).1 := by
    show _ = extGL (N_m_succ B.R) (κ.1 * z₁.1) * z₂.1⁻¹
    rw [map_mul, e₁', e₂', mul_inv_cancel_right]
  refine ⟨e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2, ?_⟩
  have e₅ : (⟨extGL (N_m_succ B.R) κ.1, e₄ ▸ ((⟨_, h⟩ : U β) * z₂⁻¹).2⟩ : U β) = (⟨_, h⟩ : U β) * z₂⁻¹ := Subtype.ext e₄
  rw [e₅, map_mul, map_inv, hc, hz₂', map_mul, hz₁', inv_one, mul_one, mul_one]

theorem extM_map {A A' : Type} [CommRing A] [CommRing A'] {N n : ℕ} (hN : N = n + 1) (f : A →+* A') (g : Matrix (Fin n) (Fin n) A) :
    (extM hN g).map f = extM hN (g.map f) := by
  ext a b
  simp only [extM, Matrix.map_apply]
  split_ifs <;> simp

theorem isExt_iff (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {R' : Type} [CommRing R']
    (φ : (I.rec7 l Z).host.E →+* R') (g' : Matrix (Fin (B.R.N B.R.m - 1)) (Fin (B.R.N B.R.m - 1)) R')
    (g : Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) R') :
    IsExt (I.rec7 l Z) (z0 X u) φ g' g ↔ g = extM (N_m_succ B.R) g' := by
  obtain ⟨-, -, hiX, -⟩ := spaces_in_coordinates I hI hP l Z
  have hN := N_m_succ B.R
  have hPr := (base_fields_primes_ok B X).2.1
  have hpi0 : ((X.piT u : 𝓞 B.host.E) : B.host.E) ≠ 0 := by
    intro h0
    have h1 : X.piT u = 0 := RingOfIntegers.ext h0
    have h2 := hPr.piT_norm u
    have h3 : (B.primes X).piT u = 0 := h1
    rw [h3, zero_mul] at h2
    exact (hPr.T_prime u).ne_zero (by exact_mod_cast h2.symm)
  have e : TC.z0 X u = z0v B X u := rfl
  constructor
  · intro hg'
    refine TilX.eq_extM_of_ext hN φ hpi0 (TilX.iXm_apply hiX hN) hg'.1 ?_
    have h2 := hg'.2
    rw [e, lastCoordinateUniformizerVector_eq_single u] at h2
    exact h2
  · rintro rfl
    refine ⟨TwP.extM_mul_incl hN g' _ fun b j => ?_, TwP.extM_mulVec_fix hN g' _ fun b hb => ?_⟩
    · refine (congrArg φ (TilX.iXm_apply hiX hN b j)).trans ?_
      by_cases h : b = Br.iC hN j
      · rw [if_pos h]
        exact (congrArg φ (if_pos h)).trans φ.map_one
      · rw [if_neg h]
        exact (congrArg φ (if_neg h)).trans φ.map_zero
    · show φ (TC.z0 X u b) = 0
      rw [e, lastCoordinateUniformizerVector_eq_single, Pi.single_eq_of_ne hb]
      exact φ.map_zero

theorem deep_twist (hI : I.Ok) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) {n T f : ℕ}
    {J : Matrix (Fin n) (Fin n) (I.rec7 l Z).host.E} (hJ : J = 1) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) J T f bad) :
    ∀ P ∈ I.Q a, ∃ N : ℕ, ∀ w ∈ UAd B.sp.cm n, Deep (F := B.host.F) P N w → w ∈ S.U := fun P hP =>
  exists_deep (I.rec7 l Z).sp.cm hJ S P (AdelicValuationDictionary.main I hI l Z a n 0 ⟨P, mem_sb I hP⟩ 1).2.1
    ((under_eq_iff B.host P _).2 (Or.inr rfl))

end Mat

section Main
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem mem_GfC_iff {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    g ∈ GfC V ↔ ((mt V g).reindex (finCongr hn) (finCongr hn)).map (infPart D) = 1 := by
  subst hn
  exact Units.ext_iff

theorem finM_of_hasMat {D : D7} {h : GA D D.sp.X'} {y} (hy : GlobalTheory.Core.Rk.Top.HasMat h y) :
    ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D))).map (toEAf D) = y.1 := by
  ext i j
  have a := hy.2 ((finCongr (rankP D)).symm i) ((finCongr (rankP D)).symm j)
  simp only [Equiv.apply_symm_apply] at a
  exact a

set_option maxHeartbeats 2000000 in

theorem emb_mem_chi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ β h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1 := by
  intro B X I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β h κ hh
  obtain ⟨-, gP, -, hsp⟩ := TC.spaces_in_coordinates I hI hP l Z
  have gN := (hsp B.R.m le_rfl).1
  have hU' : K.lev.U ≤ Formalism.L2.Col.UAd B.sp.cm (B.R.N B.R.m - 1) := fun x hx => by
    have h1 := ((K.lev.U_eq x).1 hx).1
    rw [gP] at h1
    exact h1
  obtain ⟨hm, hc⟩ := ext_mem I hI l u a (hA.reads B.R.m le_rfl)
    (fun b d g' hd => hA.top b d g' _ hd ((isExt_iff I hI hP l Z u _ _ _).2 rfl)) hK β
    (fun c => TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA c β) hU'
    (deep_twist I hI l Z a gN (A.K B.R.m le_rfl β).lev) (deep_twist I hI l Z a gP K.lev) (hA.fin B.R.m le_rfl β) hfin κ
  have he := (isExt_iff I hI hP l Z u _ _ _).1 (hemb h)
  have hG : emb h ∈ GfC _ := by
    refine (mem_GfC_iff _ (rankN (I.rec7 l Z) B.R.m le_rfl) _).2 ?_
    refine (congrArg (fun M => Matrix.map M (infPart (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_)
    exact (congrArg (TilX.extM _) ((mem_GfC_iff _ (rankP (I.rec7 l Z)) _).1 hh.1)).trans (TilX.extM_one _)
  have hF : (TilX.extGL (Formalism.L2.Col.N_m_succ B.R) κ.1).1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) := by
    refine Eq.symm ((congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) he).trans ((extM_map _ _ _).trans ?_))
    exact congrArg (TilX.extM _) (finM_of_hasMat hh)
  have hU : emb h ∈ A.U B.R.m β := (hA.U B.R.m le_rfl β _).2 ⟨hG, ⟨_, hm⟩, hF⟩
  have e : A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ := (hA.chi B.R.m le_rfl β ⟨emb h, hU⟩ ⟨_, hm⟩ hF).trans hc
  exact ⟨hU, e, e ▸ hA.norm_chi B.R.m le_rfl β _⟩

theorem levFn_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {LL : Type} [CommRing LL]
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E LL n) : ∃ m : ℕ, 0 < m ∧ ∀ x, levFn β L x ^ m = 1 := by
  let m := Nat.card L.P.H * ∏ PP ∈ L.Pg ∪ L.Q, Nat.card (kP PP)ˣ
  have hk : ∀ PP ∈ L.Pg ∪ L.Q, ∀ (φ : (kP PP)ˣ →* LLˣ) z, φ z ^ m = 1 := fun PP hPP φ z => by
    obtain ⟨d, hd⟩ : Nat.card (kP PP)ˣ ∣ m := Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hPP) _
    rw [hd, pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]
  refine ⟨m, Nat.mul_pos Nat.card_pos (Finset.prod_pos fun _ _ => Nat.card_pos), fun x => ?_⟩
  unfold levFn
  rw [mul_pow, mul_pow, ← Finset.prod_pow, ← Finset.prod_pow, Finset.prod_eq_one, Finset.prod_eq_one, mul_one, mul_one]
  · unfold ext1
    split_ifs
    · rw [pow_mul, ← map_pow, pow_card_eq_one', map_one, one_pow]
    · exact one_pow _
  · exact fun PP hPP => hk PP (Finset.mem_union_right _ hPP) _ _
  · intro PP hPP
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun c _ => hk PP (Finset.mem_union_left _ hPP) _ _

theorem chi_pow_of_levG {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C}
    {Pm : PeriodMap D.R C} {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm}
    {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) {x : GA D D.sp.X'} {J : Set (GA D D.sp.X')}
    {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {L : LevDat D.host.E ℂ D.sp.X'.rank} (h : LevG K x J (levChi _ β L)) :
    ∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1 := by
  obtain ⟨m, hm, H⟩ := levFn_pow (F := D.host.F) β L
  refine ⟨m, hm, fun κ => ?_⟩
  obtain ⟨g, hg⟩ := GlobalTheory.Core.Rk.Top.Model.hasMat_exists (D := D) ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
  have e := h.2 g κ hg
  have e2 : levChi _ β L (x⁻¹ * g * x) ^ m = 1 := by
    unfold levChi
    rw [← Units.val_pow_eq_pow_val, H, Units.val_one]
  rw [e, ← star_pow, star_eq_iff_star_eq, star_one] at e2
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, ← e2, Units.val_one])

end Main

end GlobalTheory.AdForm.LevChiTop

end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.AdForm.EvzDecomp

theorem bc_mem_UJ' {A B : Type} [CommRing A] [CommRing B] {n : Type} [Fintype n] [DecidableEq n] (φ : A →+* B) (s : A →+* A)
    (s' : B →+* B) (hs : ∀ a, φ (s a) = s' (φ a)) (J : Matrix n n A) {g : GL n A} (hg : g ∈ Formalism.UG.UJ s J) :
    Formalism.UG.bc φ g ∈ Formalism.UG.UJ s' (J.map φ) := by
  have h : Formalism.UG.cT s (g : Matrix n n A) * J * (g : Matrix n n A) = J := hg
  show Formalism.UG.cT s' ((g : Matrix n n A).map φ) * J.map φ * (g : Matrix n n A).map φ = J.map φ
  have e : Formalism.UG.cT s' ((g : Matrix n n A).map φ) = (Formalism.UG.cT s (g : Matrix n n A)).map φ := by
    ext i j; simp [Formalism.UG.cT, hs]
  rw [e, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem finM_one' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) : finM V hn (1 : GA D V) = 1 := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl]
  have e : Formalism.L2.Theta.mt V (1 : GA D V) = 1 := by
    have := GlobalTheory.AdForm.RdLaw.mt_mul V 1 1
    simpa using this
  rw [e, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finM_pf' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) :
    finM V hn (GlobalTheory.AdForm.RdLaw.pf V g) = finM V hn g := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.finM_pf V g

theorem infM_mul' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) (τ : D.what₂.Tau) :
    infM θ V hn (g * h) τ = infM θ V hn g τ * infM θ V hn h τ := by
  subst hn; exact GlobalTheory.AdForm.RdLaw.infM_mul θ V g h τ

theorem mem_GinfC_of_finM {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : finM V hn k = 1) :
    k ∈ GinfC V := by
  subst hn
  rw [GlobalTheory.AdForm.RdLaw.finM_rfl] at hk
  have e : (Formalism.L2.Theta.mt V k).map (toEAf D) = (finHom V k).val.map
      (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E) := rfl
  rw [e] at hk
  show finHom V k = 1
  apply Units.ext
  rw [Units.val_one]
  ext i j
  have := congrFun (congrFun hk i) j
  simp only [Matrix.map_apply] at this
  have h3 := congrArg (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).symm this
  rw [AlgEquiv.symm_apply_apply] at h3
  rw [h3, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem isBlock_one {R : Type} [Zero R] [One R] {N n : ℕ} (hN : N = n + 1) {G : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} (h : GlobalTheory.BranchFormula.IsBlock hN G A 1) (hA : A = 1) : G = 1 := by
  subst hN hA
  ext i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · rw [Matrix.one_apply_eq]; exact h.2.2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last b).ne']; exact (h.2.1 b).2
  · rw [Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne]; exact (h.2.1 a).1
  · have e := h.1 a b
    have e2 : G (Fin.castSucc a) (Fin.castSucc b) = (1 : Matrix (Fin n) (Fin n) R) a b := e
    rw [e2]
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (fun h => hab (Fin.castSucc_injective _ h))]

theorem ratPt {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n)
    (hG : V.gram.reindex (finCongr hn) (finCongr hn) = 1) (γ₀ : GL (Fin n) D.host.E)
    (hγ : γ₀ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) 1) :
    ∃ γ ∈ GQ V, finM V hn γ = (Formalism.UG.bc (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ₀).1 ∧
      ∀ τ, infM θ V hn γ⁻¹ τ = atInf (Formalism.L2.Forms.embT D) ((γ₀⁻¹ : GL (Fin n) D.host.E) : Matrix _ _ _) τ := by
  subst hn
  have hG' : V.gram = 1 := by simpa using hG
  have hmem : Formalism.UG.bc (incA D) γ₀ ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    have := bc_mem_UJ' (incA D) (D.sp.cm.sig : D.host.E →+* D.host.E) (sigR (AF D.host.F) D.sp.cm.sig) (fun x => ?_) 1 hγ
    · rw [hG']
      have e1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
      show Formalism.UG.bc (incA D) γ₀ ∈ Formalism.UG.UJ _ ((1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _)
      exact this
    · show sigR (AF D.host.F) D.sp.cm.sig (1 ⊗ₜ x) = _
      simp [sigR]
      rfl
  let γ : GA D V := ⟨_, hmem⟩
  have hmt : Formalism.L2.Theta.mt V γ = (γ₀ : Matrix _ _ _).map (incA D) := rfl
  have hmt' : Formalism.L2.Theta.mt V γ⁻¹ = ((γ₀⁻¹ : GL (Fin V.rank) D.host.E) : Matrix _ _ _).map (incA D) := rfl
  refine ⟨γ, ?_, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (hG' ▸ hγ))
  · exact GlobalTheory.AdForm.RdLaw.rat_finM V γ₀ γ hmt
  · intro τ
    exact GlobalTheory.AdForm.RdLaw.rat_infM θ hθ V γ₀⁻¹ γ⁻¹ hmt' τ

theorem infM_fin'' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

theorem ext_finM_emb : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m)), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (h : GA (I.rec7 l Z) (I.rec7 l Z).sp.X') (y : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) ((I.rec7 l Z).host.E ⊗[(I.rec7 l Z).host.F] FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)), GlobalTheory.Core.Rk.Top.HasMat h y → IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) y.1 (finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)) := by
  intro B X I hOk hPins l Z u emb hEmb h y hM
  obtain ⟨e1, e2⟩ := hEmb h
  have hinc : (toEAf (I.rec7 l Z)).comp (incA (I.rec7 l Z)) =
      Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
    ext x
    show (Algebra.TensorProduct.comm _ _ _) (finPart (I.rec7 l Z) (1 ⊗ₜ x)) = x ⊗ₜ 1
    have : finPart (I.rec7 l Z) (1 ⊗ₜ x) = (1 : Af (I.rec7 l Z).host.F) ⊗ₜ x := by
      show Algebra.TensorProduct.map _ _ (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
    rw [this]; rfl
  have hy : y.1 = ((Formalism.L2.Theta.mt _ h).map (toEAf (I.rec7 l Z))).reindex (finCongr (rankP (I.rec7 l Z)))
      (finCongr (rankP (I.rec7 l Z))) := by
    ext i j
    have := hM.2 ((finCongr (rankP (I.rec7 l Z))).symm i) ((finCongr (rankP (I.rec7 l Z))).symm j)
    simp only [Equiv.apply_symm_apply] at this
    rw [← this]; rfl
  refine ⟨?_, ?_⟩
  · have h3 := congrArg (fun M => Matrix.map M (toEAf (I.rec7 l Z))) e1
    simp only [Matrix.map_mul, Matrix.map_map] at h3
    rw [hy, ← hinc]
    exact h3
  · funext i
    have h3 := congrArg (toEAf (I.rec7 l Z)) (congrFun e2 i)
    rw [RingHom.map_mulVec] at h3
    rw [← hinc]
    exact h3

theorem top_lev_chi : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c (g : TC.GA B (B.R.N B.R.m)), IsExt (I.rec7 l Z) (TC.z0 X u) (Formalism.UG.inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (K.y c).1.1 g.1 → ∃ κ : (A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.U, (show TC.GA B (B.R.N B.R.m) from κ.1) = (show TC.GA B (B.R.N B.R.m) from ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1)⁻¹ * (ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)⁻¹ * g ∧ (((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).lev.chi κ : ℂˣ) : ℂ) = B.embLL (((I.stp u a B.R.m).chr (I.perIn u a).b0 ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a Ch₀ A hA bad K hRP c g hg
  have R := hA.reads B.R.m le_rfl
  have hTop := hA.top (A.chOf B.R.m ((I.perIn u a).tilC c))
  have h1 := hTop ((I.stX a).rep c).1.1 (K.y c).1 g (hRP.pt c) hg
  have hmv := (I.stp u a B.R.m).mv_smul (I.perIn u a).b0 ((I.perIn u a).tilPt c)
  have h2 := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1⁻¹ _ _ h1
  set g₀ := (I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c) with hg₀
  let κ' : (I.stp u a B.R.m).G (I.perIn u a).b0 := ((1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)), g₀.2)
  have hgam1 : (I.stp u a B.R.m).gam (I.perIn u a).b0 κ' = 1 := by
    show Formalism.L2.Col.ufGL _ _ (1 : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m)) = 1
    simp
  have hq : ((g₀.1⁻¹, 1, 1) : Formalism.L2.Col.UF B.fields.E (B.R.N B.R.m) × Formalism.L2.Col.GLG B.fields.E (B.R.N B.R.m) (B.primes X).vGs × Formalism.L2.Col.GLQ B.fields.E (B.R.N B.R.m) (Formalism.L2.Col.QE I.sel ↑(I.tup a))) • (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) =
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    have e0 : (tilF I.sel (I.tup a) u ((I.stX a).rep c).1.1) = ((I.perIn u a).tilPt c).1.1 := rfl
    rw [e0, ← hmv]
    show _ = Formalism.L2.Col.FrmG.incl _ _ κ' • _
    show _ • (Formalism.L2.Col.FrmG.incl _ _ g₀ • _) = _
    rw [smul_smul]
    congr 1
    ext1
    · simp [κ', Formalism.L2.Col.FrmG.incl]
    · ext1 <;> simp [κ', Formalism.L2.Col.FrmG.incl]
  have hr : ratAd B.host.F g₀.1⁻¹ = (ratAd B.host.F g₀.1)⁻¹ := by
    show Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1⁻¹) = (Formalism.UG.bc _ (Formalism.L2.Col.ufGL _ _ g₀.1))⁻¹
    rw [map_inv, map_inv]
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  have hpt : TC.PtOf (Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)))
      ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))).1.1 := by
    rw [← hq]
    have e : Y * (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) =
        ratAd B.host.F g₀.1⁻¹ * (g * A.kb B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c))) := by
      rw [hr]; group
    rw [e]
    exact h2
  have hcos := GlobalTheory.Mem.Col2.ChEx.cos_of_neT I (u := u) (a := a) (i := B.R.m) (by omega)
    ((I.stp u a B.R.m).act (I.perIn u a).b0 κ' ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c)))
    ((I.stp u a B.R.m).rep ((I.perIn u a).tilC c))
  have hxU := (R.lev ((I.perIn u a).tilC c) (Y⁻¹ * (ratAd B.host.F g₀.1)⁻¹ * g) _ hpt).2 ⟨κ', hgam1, rfl, hcos⟩
  refine ⟨⟨_, hxU⟩, rfl, ?_⟩
  exact R.chr ((I.perIn u a).tilC c) ⟨_, hxU⟩ κ' hgam1 hpt

end GlobalTheory.AdForm.EvzDecomp

open GlobalTheory.AdForm.EvzDecomp in

theorem GlobalTheory.AdForm.TwDat.Is.evz_decomp : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∃ γ ∈ GQ ((I.rec7 l Z).sp.X B.R.m), ∃ k ∈ GinfC ((I.rec7 l Z).sp.X B.R.m), ∃ κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)), emb h = γ * (A.h B.R.m _ ⟨(I.perIn u a).tilC c, rfl⟩ * k) * κ.1 ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ y : (I.chain l u a).Y B.R.m, ∃ y' : (I.chain l u a).Y B.R.m, IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ ∧ (A.chi B.R.m _ κ : ℂ) * φ ((I.perIn u a).tilC c) y' = (I.per l u a).evz φ c y := by
  intro B X I hOk hPins l Z u a Ch₀ A hA θ hθ emb hEmb bad K hRP c h hM
  have hExt := ext_finM_emb I hOk hPins l Z u emb hEmb h (K.y c).1 hM
  have hinvM : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, mul_inv_cancel, finM_one']
  have hinvM' : ∀ x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x⁻¹ *
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) x = 1 := fun x => by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, inv_mul_cancel, finM_one']
  let gU : TC.GA B (B.R.N B.R.m) := ⟨finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h),
    finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h)⁻¹, hinvM _, hinvM' _⟩
  obtain ⟨κ0, hκ0, hχ0⟩ := top_lev_chi I hOk hPins l Z u a Ch₀ A hA bad K hRP c gU hExt
  have hG : ((I.rec7 l Z).sp.X B.R.m).gram.reindex (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl))
      (finCongr (rankN (I.rec7 l Z) B.R.m le_rfl)) = 1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 B.R.m le_rfl).1
  obtain ⟨γ, hγQ, hγf, hγi⟩ := ratPt θ hθ _ (rankN (I.rec7 l Z) B.R.m le_rfl) hG
    (Formalism.L2.Col.ufGL _ _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
    (GlobalTheory.Mem.Col2.DnAdel.ufGL_UJ B.sp.cm _ ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1)
  obtain ⟨hh₀f, hh₀m⟩ := hA.h B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩
  set h₀ := A.h B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) ⟨(I.perIn u a).tilC c, rfl⟩ with hh₀
  set Zr := (γ * h₀)⁻¹ * emb h with hZr
  set κA := GlobalTheory.AdForm.RdLaw.pf _ Zr with hκA
  have hκAf : κA ∈ GfC _ := GlobalTheory.AdForm.RdLaw.pf_fin _ Zr
  set Y : TC.GA B (B.R.N B.R.m) := (show TC.GA B (B.R.N B.R.m) from
    ((A.K B.R.m le_rfl (A.chOf B.R.m ((I.perIn u a).tilC c))).y ⟨(I.perIn u a).tilC c, rfl⟩).1) with hY
  set Rr := ratAd B.host.F ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)).1 with hRr
  have e1 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) * finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = gU.1 := by
    rw [← GlobalTheory.AdForm.StabMove.finM_mul, hZr, mul_inv_cancel_left]
  have e2 : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) (γ * h₀) = (Rr * Y).1 := by
    rw [GlobalTheory.AdForm.StabMove.finM_mul, hγf, hh₀m]; rfl
  have e3 : (Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr) = gU.1 := by rw [← e2]; exact e1
  have hfZ : finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr = ((Rr * Y)⁻¹ * gU).1 := by
    have e4 : ((Rr * Y)⁻¹ * gU).1 = ((Rr * Y)⁻¹).1 * ((Rr * Y).1 * (show Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) from
      finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr)) := by rw [Units.val_mul, e3]
    rw [e4, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  have hκ0' : (show TC.GA B (B.R.N B.R.m) from κ0.1) = (Rr * Y)⁻¹ * gU := by rw [hκ0, _root_.mul_inv_rev]
  have hfκ : κ0.1.1 = finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) κA := by
    rw [finM_pf', hfZ, ← hκ0']
  have hκU : κA ∈ A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) :=
    (hA.U B.R.m le_rfl _ κA).2 ⟨hκAf, κ0, hfκ⟩
  let κ : A.U B.R.m (A.chOf B.R.m ((I.perIn u a).tilC c)) := ⟨κA, hκU⟩
  have hchi := hA.chi B.R.m le_rfl _ κ κ0 hfκ
  set k := Zr * κA⁻¹ with hk
  have hkC : k ∈ GinfC _ := mem_GinfC_of_finM _ (rankN (I.rec7 l Z) B.R.m le_rfl) k (by
    rw [hk, GlobalTheory.AdForm.StabMove.finM_mul, ← finM_pf' _ (rankN (I.rec7 l Z) B.R.m le_rfl) Zr, ← hκA, hinvM])
  have hInf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) (emb h) τ = 1 := fun τ =>
    isBlock_one (Formalism.L2.Col.N_m_succ B.R)
      (GlobalTheory.EmbTopBlock.isBlock_infM_emb I hOk hPins l Z u θ hθ emb (Formalism.L2.Col.N_m_succ B.R) hEmb h τ)
      (infM_fin'' θ _ (rankP (I.rec7 l Z)) h hM.1 τ)
  refine ⟨γ, hγQ, k, hkC, κ, ?_, ?_⟩
  · show emb h = γ * (h₀ * (Zr * κA⁻¹)) * κA
    rw [hZr]; group
  · intro φ _ y
    refine ⟨frMul B.fields.emb B.embLL ((I.stp u a B.R.m).gam (I.perIn u a).b0
      ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ y, ?_, ?_⟩
    · intro τ
      have ek : k = h₀⁻¹ * γ⁻¹ * (emb h * κA⁻¹) := by rw [hk, hZr]; group
      have hk' : infM θ _ (rankN (I.rec7 l Z) B.R.m le_rfl) k τ = ((((I.stp u a B.R.m).gam (I.perIn u a).b0
          ((I.stp u a B.R.m).mv (I.perIn u a).b0 ((I.perIn u a).tilPt c)))⁻¹ : GL (Fin (B.R.N B.R.m)) B.fields.E) :
            Matrix (Fin (B.R.N B.R.m)) (Fin (B.R.N B.R.m)) B.fields.E).map (Formalism.L2.Col.embAt B.embLL B.fields.emb τ) := by
        rw [ek, infM_mul', infM_mul', infM_mul', infM_fin'' θ _ _ h₀⁻¹ (inv_mem hh₀f), hInf,
          infM_fin'' θ _ _ κA⁻¹ (inv_mem hκAf), one_mul, mul_one, mul_one, hγi τ,
          GlobalTheory.Mem.Col2.LowerTie.embT_eq I l Z]
        rfl
      rw [hk']
      rfl
    · rw [hchi, hχ0]
      rfl
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem rd_emb_evz : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ : ℕ → Type) (A : TwDat I l Z u a Ch₀), A.Is → ∀ θ, IsInfFam θ → ∀ emb : GA (I.rec7 l Z) (I.rec7 l Z).sp.X' →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m), IsEmbTop (D := (I.rec7 l Z)) (TC.z0 X u) emb → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → ∀ β, ((∃ n : ℕ, 0 < n ∧ ∀ κ, K.lev.chi κ ^ n = 1) → ∀ h (κ : K.lev.U), GlobalTheory.Core.Rk.Top.HasMat h κ.1 → ∃ hU : emb h ∈ A.U B.R.m β, A.chi B.R.m β ⟨emb h, hU⟩ = K.lev.chi κ ∧ ‖((K.lev.chi κ : ℂˣ) : ℂ)‖ = 1) ∧ ∀ φ ∈ (I.fm l u a).Fi B.R.m, ∀ c h, GlobalTheory.Core.Rk.Top.HasMat h (K.y c).1 → ∀ y, A.rd θ B.R.m le_rfl β φ y (emb h) = (I.per l u a).evz φ c y := by
  intro B X I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK β
  refine ⟨fun hfin => GlobalTheory.AdForm.LevChiTop.emb_mem_chi I hI hP l Z u a Ch₀ A hA emb hemb bad K hK hfin β, ?_⟩
  intro φ hφ c h hh y
  have hβ := GlobalTheory.AdForm.TwDat.Is.chOf_top_eq I hI hP l Z u a Ch₀ A hA ((I.perIn u a).tilC c) β
  subst hβ
  obtain ⟨γ, hγ, k, hk, κ, he, hv⟩ := GlobalTheory.AdForm.TwDat.Is.evz_decomp I hI hP l Z u a Ch₀ A hA θ hθ emb hemb bad K hK c h hh
  obtain ⟨y', hy', hval⟩ := hv φ hφ y
  rw [he, (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch₀ A hA θ hθ B.R.m le_rfl φ hφ).2 _ y γ hγ ⟨(I.perIn u a).tilC c, rfl⟩ k hk κ y' hy']
  exact hval

end GlobalTheory.AdForm
end
