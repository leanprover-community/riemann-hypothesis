import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ClassPresBasic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield

section
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

noncomputable section

namespace GlobalTheory.PresRat

def conjAlg : algebraicClosure ℚ ℂ →+* algebraicClosure ℚ ℂ :=
  ((starRingEnd ℂ).comp (algebraicClosure ℚ ℂ).val.toRingHom).codRestrict (algebraicClosure ℚ ℂ) fun x => by
    have hx : IsAlgebraic ℚ (x : ℂ) := mem_algebraicClosure_iff.1 x.2
    exact mem_algebraicClosure_iff.2 (hx.algHom (starRingEnd ℂ).toRatAlgHom)

def cmComplex : Subfield ℂ :=
  (⨅ τ : algebraicClosure ℚ ℂ →+* ℂ, RingHom.eqLocusField (τ.comp conjAlg) ((starRingEnd ℂ).comp τ)).map
    (algebraicClosure ℚ ℂ).val.toRingHom

theorem mem_cmComplex {z : ℂ} : z ∈ cmComplex ↔ ∃ x : algebraicClosure ℚ ℂ, (x : ℂ) = z ∧
    ∀ τ : algebraicClosure ℚ ℂ →+* ℂ, τ (conjAlg x) = starRingEnd ℂ (τ x) := by
  unfold cmComplex
  rw [Subfield.mem_map]
  refine exists_congr fun x => ?_
  rw [Subfield.mem_iInf, and_comm]
  rfl

theorem conj_eq_inv_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : starRingEnd ℂ z = z⁻¹ :=
  (Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one hz hn.ne')).symm

theorem mem_cmComplex_of_pow {z : ℂ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) : z ∈ cmComplex := by
  have ha : IsAlgebraic ℚ z := IsAlgebraic.of_pow hn (by rw [hz]; exact isAlgebraic_one)
  refine mem_cmComplex.2 ⟨⟨z, mem_algebraicClosure_iff.2 ha⟩, rfl, fun τ => ?_⟩
  set x : algebraicClosure ℚ ℂ := ⟨z, mem_algebraicClosure_iff.2 ha⟩
  have hx : x ^ n = 1 := Subtype.ext hz
  have h1 : conjAlg x = x⁻¹ := Subtype.ext (conj_eq_inv_of_pow hn hz)
  rw [h1, map_inv₀, conj_eq_inv_of_pow hn (by rw [← map_pow, hx, map_one])]

theorem mem_cmComplex_iff {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (a : K) : σ a ∈ cmComplex ↔ a ∈ cmMax K := by
  let s : K →+* algebraicClosure ℚ ℂ := σ.codRestrict (algebraicClosure ℚ ℂ) fun x =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)
  have hs : conjAlg (s a) = s (star a) := Subtype.ext (hσ a).symm
  rw [mem_cmComplex]
  constructor
  · rintro ⟨x, hx, h⟩ φ
    have hx' : x = s a := Subtype.ext hx
    let _ : Algebra K (algebraicClosure ℚ ℂ) := s.toAlgebra
    have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := by
      convert algebraicClosure.isAlgebraic ℚ ℂ
      · rfl
      · exact Subsingleton.elim _ _
    have : Algebra.IsAlgebraic K (algebraicClosure ℚ ℂ) :=
      Algebra.IsAlgebraic.tower_top (K := ℚ) K
    have h1 := h (ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ)
    rw [hx', hs] at h1
    have e : ∀ b, ComplexEmbedding.lift (algebraicClosure ℚ ℂ) φ (s b) = φ b := fun b =>
      ComplexEmbedding.lift_algebraMap_apply _ φ b
    rw [e, e] at h1
    exact h1
  · intro h
    exact ⟨s a, rfl, fun τ => by rw [hs]; exact h (τ.comp s)⟩

variable {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K]
  [NumberField K] [StarRing K] {ι : Γ →* G} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W}
  {J : Subgroup G} {χ : J →* ℂˣ} (P : ClassPres ι S σ ρ J χ)

theorem act_mem (hσ : ∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) (hχ : ∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1)
    (hρ : ∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i))
    (k : J) (γ : Γ) (x : S.V) (hx : ∀ i, S.bV.repr x i ∈ cmMax K) (i : S.ιV) :
    (PresBasic.bW P).repr ((χ k : ℂ) • ρ γ (P.coef x)) i ∈ cmComplex := by
  obtain ⟨n, hn, hk⟩ := hχ k
  have h1 : (χ k : ℂ) ∈ cmComplex :=
    mem_cmComplex_of_pow hn (by rw [← Units.val_pow_eq_pow_val, hk, Units.val_one])
  have h2 : P.coef x = ∑ j, σ (S.bV.repr x j) • P.coef (S.bV j) := by
    conv_lhs => rw [← S.bV.sum_repr x]
    rw [map_sum]
    simp only [map_smulₛₗ]
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, h2]
  refine cmComplex.mul_mem h1 ?_
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine cmComplex.sum_mem fun j _ => cmComplex.mul_mem ((mem_cmComplex_iff σ hσ _).2 (hx j)) ?_
  obtain ⟨c, hc, e⟩ := hρ γ j
  rw [e]
  simp only [← PresBasic.bW_apply]
  rw [Module.Basis.repr_sum_self]
  exact (mem_cmComplex_iff σ hσ _).2 (hc i)

end GlobalTheory.PresRat

namespace GlobalTheory

theorem classPres_dcOp_rat : ∀ {G Γ W K : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K] [StarRing K] (ι : Γ →* G) (S : CSD K) (σ : K →+* ℂ) (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (P : ClassPres ι S σ ρ J χ) (A : Finset G) (T : Module.End K S.Forms), (∀ a : K, σ (star a) = starRingEnd ℂ (σ a)) → (∀ k, ∃ n : ℕ, 0 < n ∧ χ k ^ n = 1) → (∀ γ j, ∃ c : S.ιV → K, (∀ i, c i ∈ cmMax K) ∧ ρ γ (P.coef (S.bV j)) = ∑ i, σ (c i) • P.coef (S.bV i)) → (∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp A (P.ext (f : S.Cl → S.V))) → S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax K := by
  intro G Γ W K _ _ _ _ _ _ _ ι S σ ρ J χ P A T hσ hχ hρ hT
  have hb : S.HasRatBasis := by
    refine (forms_rat S).1 fun c γ i j => ?_
    rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, P.coef_act]
    refine PresRat.act_mem P hσ hχ hρ _ _ _ (fun l => ?_) i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨hb, (forms_rat S).2 T hb fun f hf c i => ?_⟩
  rw [← PresRat.mem_cmComplex_iff σ hσ, ← PresBasic.repr_coef P, ← PresBasic.ext_y P, hT]
  unfold dcOp
  rw [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  exact PresRat.cmComplex.sum_mem fun a _ => PresRat.act_mem P hσ hχ hρ _ _ _ (hf _) i

end GlobalTheory
end
end

section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Links NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeRational

open Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Bridge Formalism.L2.Theta
open scoped TensorProduct

theorem repr_mem_of_basis_rational {K V ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype ι] [Fintype κ]
    (F : Subfield K) (b : Module.Basis ι K V) (b' : Module.Basis κ K V) (h : ∀ i j, b'.repr (b i) j ∈ F)
    (v : V) (hv : ∀ j, b'.repr v j ∈ F) (i : ι) : b.repr v i ∈ F := by
  obtain ⟨φ, h1, h2⟩ := FormsDescent.exists_retraction F
  have e2 : FormsDescent.coordMap F b' φ v = v := by
    apply b'.repr.injective
    ext j
    rw [FormsDescent.repr_coordMap, h2 _ (hv j)]
  have key : v = ∑ a, φ (b.repr v a) • b a := by
    rw [← FormsDescent.coordMap_sum F b' φ _ _ h, b.sum_repr, e2]
  have : b.repr v i = φ (b.repr v i) := by
    conv_lhs => rw [key]
    rw [b.repr_sum_self]
  rw [this]
  exact h1 _

theorem repr_map_mem {K V κ : Type} [Field K] [AddCommGroup V] [Module K V] [Fintype κ]
    (F : Subfield K) (b : Module.Basis κ K V) (g : V →ₗ[K] V) (hg : ∀ i j, b.repr (g (b j)) i ∈ F)
    (v : V) (hv : ∀ j, b.repr v j ∈ F) (i : κ) : b.repr (g v) i ∈ F := by
  have h1 : g v = ∑ j, b.repr v j • g (b j) := by
    conv_lhs => rw [← b.sum_repr v]
    simp only [map_sum, map_smul]
  rw [h1]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  exact F.sum_mem fun j _ => F.mul_mem (hv j) (hg i j)

theorem levFn_isOfFinOrder {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : Formalism.L2.DIV.LevDat E ℂ n) (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    IsOfFinOrder (levFn β L x) := by
  have hfin : ∀ PP : Pl E, Finite (kP PP) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hone : IsOfFinOrder (1 : ℂˣ) := IsOfFinOrder.one
  unfold levFn
  refine IsOfFinOrder.mul (IsOfFinOrder.mul ?_ ?_) ?_
  · unfold ext1
    split_ifs
    · exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
    · exact hone
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun c _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)
  · refine Finset.prod_induction _ IsOfFinOrder (fun _ _ => IsOfFinOrder.mul) hone fun PP _ => ?_
    exact MonoidHom.isOfFinOrder _ (isOfFinOrder_of_finite _)

variable {D : D7}

theorem levEnv_chi_pow (V : TH.HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J) : ∃ n : ℕ, 0 < n ∧ (levEnv V β L).χ k ^ n = 1 :=
  isOfFinOrder_iff_pow_eq_one.1 (levFn_isOfFinOrder β (Lev.flag1L L) _)

theorem embE_mem_cmMax (x : D.host.E) : D.embE x ∈ cmMax D.what₂.LL := by
  intro σ
  rw [← D.embE_conj]
  exact D.host.conjE_apply (σ.comp D.embE) x

theorem labLL_mem_cmMax (τ : D.what₂.Tau) (x : D.host.E) : labLL D τ x ∈ cmMax D.what₂.LL := embE_mem_cmMax _

theorem action_rational (V : TH.HSp D) (C : CoefDat D V) {S : CSD D.what₂.LL} {J : Subgroup (Gf V)} {χ : J →* ℂˣ}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ J χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL) (γ : GQ V) (j : S.ιV) :
    ∃ c : S.ιV → D.what₂.LL, (∀ i, c i ∈ cmMax D.what₂.LL) ∧
      C.ρ γ (P.coef (S.bV j)) = ∑ i, D.what₂.embLL (c i) • P.coef (S.bV i) := by
  obtain ⟨e, hr, he, -⟩ := hP
  obtain ⟨γE, hγ⟩ : ∃ γE, IsRatMat V γ γE := by
    obtain ⟨g, hg⟩ := γ.2
    exact ⟨g, hg.2.symm⟩
  refine ⟨fun i => (S.bV.map e).repr (rho γE (e (S.bV j))) i, fun i => ?_, ?_⟩
  · exact repr_mem_of_basis_rational _ (S.bV.map e) (bVV D.what₂.LL lam) hr _
      (repr_map_mem _ _ _ (hrho γE) _ (hr j)) i
  · rw [he, ← hM.1 γ γE hγ]
    conv_lhs => rw [← (S.bV.map e).sum_repr (rho γE (e (S.bV j)))]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he, LinearMap.map_smulₛₗ, Module.Basis.map_apply]

theorem dcOp_matrix_mem_cmMax (V : TH.HSp D) (C : CoefDat D V) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) {S : CSD D.what₂.LL}
    (P : ClassPres (ratF V) S D.what₂.embLL C.ρ (levEnv V β L).J (levEnv V β L).χ) {lam : D.what₂.Tau → DomWeight V.rank}
    {c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] C.W} {pair nab del}
    {rho : GL (Fin V.rank) D.host.E →* Module.End D.what₂.LL (VV D.what₂.LL lam)}
    (hP : CoefTie V C P lam c0 pair nab del) (hM : CoefMapTie V C c0 rho)
    (hrho : ∀ g i j, (bVV D.what₂.LL lam).repr (rho g (bVV D.what₂.LL lam j)) i ∈ cmMax D.what₂.LL)
    (B : Finset (Gf V)) (T : Module.End D.what₂.LL S.Forms)
    (hT : ∀ f : S.Forms, P.ext ((T f : S.Forms) : S.Cl → S.V) = dcOp B (P.ext (f : S.Cl → S.V))) :
    S.HasRatBasis ∧ ∀ a b, LinearMap.toMatrix S.basis S.basis T a b ∈ cmMax D.what₂.LL :=
  GlobalTheory.classPres_dcOp_rat (ratF V) S D.what₂.embLL C.ρ _ _ P B T D.starLL_cx (levEnv_chi_pow V β L)
    (action_rational V C P hP hM hrho) hT

theorem toMatrix_one_mem {K M ι : Type} [Field K] [AddCommGroup M] [Module K M] [Fintype ι] [DecidableEq ι] (F : Subfield K)
    (b : Module.Basis ι K M) (i j : ι) : LinearMap.toMatrix b b (1 : Module.End K M) i j ∈ F := by
  rw [LinearMap.toMatrix_one, Matrix.one_apply]
  split_ifs
  · exact F.one_mem
  · exact F.zero_mem

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem rows_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (t : T) (B : Finset (Gf D.sp.X'))
    (U : Module.End D.what₂.LL (A.MtildeCSD t).Forms)
    (hU : ∀ f : (A.MtildeCSD t).Forms, (R.B.R t).pres.ext (U f).1 = dcOp B ((R.B.R t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtildeCSD t).basis (A.MtildeCSD t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax D.sp.X' R.cX.coef R.βX (R.datXt t) (R.B.R t).pres (hT.coefR t) hT.mapR
    (fun g i j => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i j).1) B U hU).2 a b

theorem lifts_dcOp_mem_cmMax (R : RealDat D A Ks) (h : R.fam_tie) (j : Fin D.R.m) (t : T) (B : Finset (Gf (Vc D j)))
    (U : Module.End D.what₂.LL (A.MtCSD j t).Forms)
    (hU : ∀ f : (A.MtCSD j t).Forms, (R.B.L j t).pres.ext (U f).1 = dcOp B ((R.B.L j t).pres.ext f.1)) (a b) :
    LinearMap.toMatrix (A.MtCSD j t).basis (A.MtCSD j t).basis U a b ∈ cmMax D.what₂.LL := by
  obtain ⟨gramR, c0R, c0L, hT⟩ := h
  exact (dcOp_matrix_mem_cmMax (Vc D j) (R.cV j).coef (R.βV j) (R.datVt j t) (R.B.L j t).pres (hT.coefL j t) (hT.mapL j)
    (fun g i k => (coefAction_repr_mem_subfield (labLL D) _ _ labLL_mem_cmMax g i k).2) B U hU).2 a b


end GlobalTheory.HeckeRational

end
end
