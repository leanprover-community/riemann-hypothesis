import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSupStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeInIsotypicSup
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.FormsStep
theorem goodPart_le_iSup_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b hj1 hj2
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b hj1 hj2
  have ha := descend_actL D T S In i j b hj1 hj2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  refine (GlobalTheory.T.V0T_le_span_image_goodL D S In T i j b hj1 hj2 (eIdem_all D) Φ hc ha he hw).trans (Submodule.span_le.mpr ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe]
  refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ (In.span j hj1 hj2 hx) ?_ ?_ ?_
  · intro σ y hy
    refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ hy ?_ ?_ ?_
    · intro hσ z hz
      refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ?_)
      rw [Submodule.mem_inf] at hz ⊢
      refine ⟨descend_mem_V0T D T S In i j b Φ hc ha he z hz.1, ?_⟩
      have hz2 := hz.2
      simp only [Submodule.mem_iInf] at hz2 ⊢
      intro k P hkP
      have hPb : P ∉ In.Sb := fun hP => hkP.2.2.2 (by
        rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
        exact Or.inr (Finset.mem_coe.mpr (hSb hP)))
      exact descend_mem_eigenspace D T S In i j b hj1 hj2 Φ hc hf k P _ z (hz2 k P ⟨hkP.1, hkP.2.1, hkP.2.2.1, hPb⟩)
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
  · rw [map_zero]; exact zero_mem _
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz
end GlobalTheory.HeightCounting.FormsStep
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_in_isotypic_sup_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.FormsStep.goodPart_le_iSup_eigen_alt
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.HeightCounting.FormsStep
section SigMake
variable (D : D7) (T : TwR D.LL0 D.nd) {S : RatDat D.ntw} (In : RatIn D S)
end SigMake
theorem span_eig_BI_alt (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In) (hSb : In.Sb ⊆ Sx) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0)
    (hsp : ∀ i j b, Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤)
    (i : T.Tw) (j : ℕ) (b : Bool) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    Submodule.span (FractionRing (T.O i))
      {y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) | ∃ σ : D.what₂.FT,
        (D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ) ∧ ∀ k P, sigVal D T i k P →
          (hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y = sigLam D T In i j b σ k P • y} = ⊤ := by
  obtain ⟨e, he_inj, he_rng, he_tm'⟩ : ∃ e : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) →ₗ[FractionRing (T.O i)]
      FmT D T S i j b, Function.Injective e ∧ LinearMap.range e = V0T D T S In.rho In.chi In.θ i j b ∧
      ∀ (c : FractionRing (T.O i)) (x : ↥(BI D T S In i j b)), e (c ⊗ₜ[T.O i] x) = c • (x : FmT D T S i j b) :=
    GlobalTheory.T.exists_injective_baseChange_inf_restrictScalars_range_eq (BsupT D T S i j b) (hsp i j b) (V0T D T S In.rho In.chi In.θ i j b)
  have hcomm : ∀ k P, sigVal D T i k P → ∀ y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b),
      e ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y) = hkT D T S In i j b k P (e y) := by
    intro k P hv y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => rw [LinearMap.baseChange_tmul, he_tm', he_tm', map_smul, hkB_coe_of_val D T In hst i j b k P h1 h2 hv]
    | add y z hy hz => simp only [map_add, hy, hz]
  have key : V0T D T S In.rho In.chi In.θ i j b ≤ Submodule.map e (Submodule.span (FractionRing (T.O i))
      {y : FractionRing (T.O i) ⊗[T.O i] ↥(BI D T S In i j b) | ∃ σ : D.what₂.FT,
        (D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ) ∧ ∀ k P, sigVal D T i k P →
          (hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i)) y = sigLam D T In i j b σ k P • y}) := by
    refine le_trans (_root_.GlobalTheory.T.lattice_in_isotypic_sup_alt D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b h1 h2) ?_
    refine iSup₂_le fun σ hσ => ?_
    intro x hx
    obtain ⟨hx0, hx1⟩ := Submodule.mem_inf.mp hx
    rw [← he_rng] at hx0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx0
    refine Submodule.mem_map_of_mem (Submodule.subset_span ⟨σ, hσ, fun k P hv => he_inj ?_⟩)
    rw [hcomm k P hv, map_smul]
    simp only [Submodule.mem_iInf] at hx1
    exact Module.End.mem_eigenspace_iff.mp (hx1 k P hv)
  rw [eq_top_iff]
  intro y _
  have hy : e y ∈ Submodule.map e _ := key (he_rng ▸ LinearMap.mem_range_self e y)
  obtain ⟨z, hz, hze⟩ := Submodule.mem_map.mp hy
  rw [← he_inj hze]
  exact hz
theorem sig_of_fg_alt (hfg : ∀ (D : D7) (S : RatDat D.ntw) (In : RatIn D S) (T : TwR D.LL0 D.nd) (i : T.Tw) (j : ℕ) (b : Bool),
    (BsupT D T S i j b).FG ∧
      Submodule.span (FractionRing (T.O i)) (BsupT D T S i j b : Set (FmT D T S i j b)) = ⊤) : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 := by
  intro D cf jE A S In b0 b1 Sx T Sp hst hSb hstar
  refine ⟨sigDataOf D T In, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j b h1 h2
    haveI : Module.Finite (T.O i) ↥(BI D T S In i j b) :=
      Module.Finite.iff_fg.mpr (fg_BI D T S In (fun i j b => (hfg D S In T i j b).1) i j b)
    rw [eq_top_iff, ← _root_.GlobalTheory.HeightCounting.FormsStep.span_eig_BI_alt D cf jE A S In b0 b1 Sx T Sp hst hSb hstar (fun i j b => (hfg D S In T i j b).2) i j b h1 h2]
    refine Submodule.span_le.mpr ?_
    rintro y ⟨σ, hσ, hy⟩
    by_cases hy0 : y = 0
    · rw [hy0]
      exact Submodule.zero_mem _
    have hint : ∀ k P, sigVal D T i k P → ∃ a : T.O i,
        algebraMap (T.O i) (FractionRing (T.O i)) a = sigLam D T In i j b σ k P :=
      fun k P hv => eigenvalue_integral_of_baseChange _ y hy0 _ (hy k P hv)
    let x : SigIdx D T In i := ⟨(⟨j, Nat.lt_succ_of_le h2⟩, b, σ), h1, hσ.1, hσ.2, hint⟩
    refine Submodule.subset_span ⟨⟨sigSys D T In i x, x, rfl⟩, rfl, rfl, fun k P hk1 hk2 hsp hP => ?_⟩
    rw [hy k P ⟨hk1, hk2, hsp, hP⟩]
    congr 1
    exact (sigEig_on D T In i x k P ⟨hk1, hk2, hsp, hP⟩).symm
  · intro i s s' h1 h2 h3
    have e1 := sigDataOf_spec D T In i s
    have e2 := sigDataOf_spec D T In i s'
    apply Subtype.ext
    refine Prod.ext h1 (Prod.ext h2 ?_)
    funext k P
    by_cases hv : sigVal D T i k P
    · exact h3 k P hv.1 hv.2.1 hv.2.2.1 hv.2.2.2
    · change s.1.2.2 k P = s'.1.2.2 k P
      rw [← e1, ← e2]
      change sigEig D T In i _ k P = sigEig D T In i _ k P
      rw [sigEig_off D T In i _ k P hv, sigEig_off D T In i _ k P hv]
  · intro i s
    have e1 := sigDataOf_spec D T In i s
    have hj : s.1.1 = (s.2.choose.1.1 : ℕ) := (congrArg Prod.fst e1).symm
    show D.what₂.isot s.1.1 s.2.choose.1.2.2 ≠ ⊥ ∧ D.nd.goodRow s.2.choose.1.2.2
    rw [hj]
    exact ⟨s.2.choose.2.2.1, s.2.choose.2.2.2.1⟩
  · intro i s k P hk1 hk2 hsp hP
    have e1 := sigDataOf_spec D T In i s
    have hj : s.1.1 = (s.2.choose.1.1 : ℕ) := (congrArg Prod.fst e1).symm
    have hb : s.1.2.1 = s.2.choose.1.2.1 := (congrArg (fun p => p.2.1) e1).symm
    have hh : s.1.2.2 = sigEig D T In i s.2.choose := (congrArg (fun p => p.2.2) e1).symm
    show algebraMap (T.O i) (FractionRing (T.O i)) (s.1.2.2 k P) =
      algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i s.1.2.1 P : T.O i) ^ k *
        readT D T i s.1.2.1 (In.eig s.1.1 s.2.choose.1.2.2 k P)
    rw [hh, hj, hb]
    exact sigEig_on D T In i _ k P ⟨hk1, hk2, hsp, hP⟩
  · intro i s P
    have e1 := sigDataOf_spec D T In i s
    have hh : s.1.2.2 = sigEig D T In i s.2.choose := (congrArg (fun p => p.2.2) e1).symm
    show s.1.2.2 0 P = 1
    rw [hh]
    exact sigEig_off D T In i _ 0 P (fun h => absurd h.1 (by omega))
theorem sigData_exists_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 :=
  _root_.GlobalTheory.HeightCounting.FormsStep.sig_of_fg_alt bsupT_fg_span_all
end GlobalTheory.HeightCounting.FormsStep
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_data_span_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T)
    (hst : HkStab D T S In), In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∃ sd : SigData D T,
      (∀ i j b, 1 ≤ j → j ≤ D.R.m →
        Submodule.span (FractionRing (T.O i))
          {x : TensorProduct (T.O i) (FractionRing (T.O i)) ↥(BI D T S In i j b) | ∃ s : sd.Sig i, sd.jS i s = j ∧
            sd.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
              ((hkB D T S In hst i j b k P).baseChange (FractionRing (T.O i))) x =
                algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) • x} = ⊤) ∧
      (∀ i (s s' : sd.Sig i), sd.jS i s = sd.jS i s' → sd.side i s = sd.side i s' →
        (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i → sd.hEig i s k P = sd.hEig i s' k P) → s = s') ∧
      (∀ i s, D.what₂.isot (sd.jS i s) (sd.rowS i s) ≠ ⊥ ∧ D.nd.goodRow (sd.rowS i s)) ∧
      (∀ i s k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ T.S0 i →
        algebraMap (T.O i) (FractionRing (T.O i)) (sd.hEig i s k P) =
          algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i (sd.side i s) P : T.O i) ^ k *
            readT D T i (sd.side i s) (In.eig (sd.jS i s) (sd.rowS i s) k P)) ∧
      ∀ i s P, sd.hEig i s 0 P = 1 := by
  atlas_forward_decl _root_.GlobalTheory.HeightCounting.FormsStep.sigData_exists_alt
end
end
