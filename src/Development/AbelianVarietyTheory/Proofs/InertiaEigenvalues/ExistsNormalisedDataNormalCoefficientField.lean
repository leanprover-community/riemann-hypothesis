import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffCurveOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionFramedPointsIsActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseTuplePinsOrientationStandardFrameLevelMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientMapExtensionRationalValuesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPlaceDatumOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSideOfModelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientMapUniqueBijectiveComplexExtensionStatement
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFirstOfSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataGivenLevelCoeffMaps

section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneCover

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover

variable {D : D7}

set_option maxHeartbeats 1000000 in

theorem exists_fun_cover {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hA : d.l₂.A = 1) :
    ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
      IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
        (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
            (IntermediateField.inclusion d.c₂.le).toRingHom)
          (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
        (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
        (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
        ∀ (_ : d.IsLev) (_ : FnAlgClosed d.Xo₂ d.c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
          (_ : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
            (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
            xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
          (_ : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
          (m : ℕ) (_ : 0 < m) (_ : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
          (_ : zeta m ∈ c.F),
          ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
            ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
              rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
                1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  refine ⟨C.unf un, dict, hP.unf, hP.modelW, g, e, F, ik, φ, th, hth, ?_, ?_⟩
  · rw [← hCι, ← hCx]
    exact hdl
  intro hlev hcl xi h1 h2 m hm h3 hz
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ GlobalTheory.NormOneChar.mem_of_pow_eq_one hm hz (by
      rw [← Units.val_pow_eq_pow_val, h3 h, Units.val_one])⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem halfIs_of_eq {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {t t' : T0}
    (e : R.Q t' = R.Q t) {Mb I : Ideal (𝓞 D.host.E)} (h : HalfIs R t' Mb I) : HalfIs R t Mb I := by
  unfold HalfIs at h ⊢
  rwa [e] at h

theorem xi_pow_eq_one (D : D7) (c : (AE D)ˣ →* Circle) (χ : HChar D.host.E) (h : ChrEq c χ) (n : ℕ)
    (ho : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 :=
  GlobalTheory.T.heckeChar_eq_one_of_trivial_finitePartOne D (c ^ n) ⟨h.1.1.pow n, fun x => by
    rw [MonoidHom.pow_apply, h.1.2, one_pow]⟩ (GlobalTheory.T.idelicCharacter_pow_eq_one_finiteIdeles_of_orderDvd D c χ h n ho) x

def CoversRep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H) (rep : T0 → T0) (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) : Prop :=
  ∃ (d : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)
    (U : ∀ t, Unf (d t).Xo₂ (d t).c₂ ((inC c').comp ((d t).eF.symm : (d t).c₂.F →+* c'.F)) D.R.r)
    (dict : ∀ t, GA D (Wc D i) → Σ k, Frame ((U t).X k).Ψ D.R.r)
    (f : ∀ t, Rul (d (rep t)).Xo₂ (d (rep t)).c₂)
    (xi : T0 → (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ),
    (∀ t, (d t).pd = pd t ∧ (d t).I = I t ∧ (d t).l₂ = l₂ t) ∧
    CovPin (T.Q.Xo ((i : ℕ) + 1)) c' (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n)) ∧
    (∀ t, HalfIs R t T.Q.l.Mb (d (rep t)).I) ∧
    (∀ t, XiIs R i t (xi t)) ∧
    CXiVal (Wc D i) (rank_Wc i) (inC c') (fun t => ({ d (rep t) with cδ := f t } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n))
      (fun t => U (rep t)) (fun t => dict (rep t)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) xi ∧
    (∀ t k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k))

set_option maxHeartbeats 2000000 in

theorem exists_covers_rep (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) {μ0 : T0} [Finite T0]
    (hT : LawsJ T) (hL : R.toLevCh.Is μ0) (i : Fin D.R.m) (n : ℕ)
    (pd : T0 → ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (pd t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (rep : T0 → T0) (hrep : ∀ t, R.Q (rep t) = R.Q t) :
    ∃ c₁ : Coeff T.Q.l, T.Q.c.F ≤ c₁.F ∧ D.what₂.embLL.toRatAlgHom.fieldRange ≤ c₁.F ∧
      (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ c₁.F) ∧
      ∀ (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c₁.F ≤ c'.F → CoversRep T R i n pd I l₂ rep c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  have hX : ∀ t, ∃ (Xo₂ : Moduli (T.Q.Dw ((i : ℕ) + 1)) (l₂ t)) (c₀ : Coeff (l₂ t)),
      ∀ c'' : Coeff (l₂ t), c₀.F ≤ c''.F → FnAlgClosed Xo₂ c'' := fun t => by
    obtain ⟨Xo₂⟩ := GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₀, -⟩ := exists_coeff_ge (l₂ t) ⊥
    obtain ⟨c₁, -, h⟩ := (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ Xo₂ c₀ hpos).2
    exact ⟨Xo₂, c₁, h⟩
  choose Xo₂ c₀ hc₀ using hX
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have := T.Q.c.fin
  have : ∀ t, FiniteDimensional ℚ (c₀ t).F := fun t => (c₀ t).fin
  have : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {zeta (m t)}) := fun t =>
    IntermediateField.adjoin.finiteDimensional
      ((Complex.isPrimitiveRoot_exp (m t) (hm t).ne').isIntegral (hm t)).tower_top
  have : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
    LinearEquiv.finiteDimensional (D.what₂.embLL.toRatAlgHom.equivFieldRange).toLinearEquiv
  obtain ⟨c₁, hc₁⟩ := exists_coeff_ge T.Q.l ((T.Q.c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange) ⊔
    ⨆ t, ((c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}))
  have hsup₁ : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c₁.F := fun t =>
    ((le_iSup (fun t => (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)}) t).trans le_sup_right).trans hc₁
  refine ⟨c₁, (le_sup_left.trans le_sup_left).trans hc₁, (le_sup_right.trans le_sup_left).trans hc₁, fun t x => ?_, fun c' hle hc' => ?_⟩
  · refine GlobalTheory.NormOneChar.mem_of_pow_eq_one (hm t) (hsup₁ t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _))) ?_
    rw [← Circle.coe_pow, xi_pow_eq_one D (R.xi t) (R.xiH t) (hL.xi t) (m t) (ho t) x]
    rfl
  have hsup : ∀ t, (c₀ t).F ⊔ IntermediateField.adjoin ℚ {zeta (m t)} ≤ c'.F := fun t => (hsup₁ t).trans hc'
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    have h0 : (c₀ t).F ≤ c'.F := le_sup_left.trans (hsup t)
    let c₂ : Coeff (l₂ t) := ⟨c'.F, c'.fin, c'.conj, h0 (c₀ t).zeta_mem, (c₀ t).le.trans h0⟩
    have hd := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n (pd t) (I t) (l₂ t) (Xo₂ t) c₂ rfl
      l1 l2 l3 l4 l5
    have hd' : ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = pd t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧ d.l₂.A = 1 ∧
        FnAlgClosed d.Xo₂ d.c₂ ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
      obtain ⟨⟨pd', I', l₂', Xo₂', c₂', hF, r, mm, nab, cδ, φ₀⟩, a1, a2, a3, e₁, e₂, -, a4, a5⟩ := hd
      refine ⟨_, a1, a2, a3, a4, a3 ▸ l6, ?_, a5⟩
      dsimp only at a3 e₁ e₂ ⊢
      subst a3
      obtain rfl := eq_of_heq e₁
      obtain rfl := eq_of_heq e₂
      exact hc₀ t c₂ h0
    exact hd'
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH (rep t)).2.1 PP (by rw [hrep]; exact hPP) ?_
    have h1 : (((d (rep t)).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d (rep t)).l₂.Mb :=
      Ideal.mul_le_left ((d (rep t)).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 (rep t)).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  choose U dict b3 using fun t => exists_fun_cover (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a5 t)
  have b4 : ∀ t, ∃ f : Rul (d (rep t)).Xo₂ (d (rep t)).c₂,
      ({ d (rep t) with cδ := f } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n).IsLev ∧ f ^ m t = 1 ∧
      IsUnf (U (rep t)) ∧ (∀ k, ModelW (Wc D i) (rank_Wc i) ((U (rep t)).X k)) ∧
      ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ))
        (F : FamilyUnif (d (rep t)).Xo₂ (((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)).comp
            (IntermediateField.inclusion (d (rep t)).c₂.le).toRingHom)
          (fun j => relab (d (rep t)).c₂ ((inC c').comp ((d (rep t)).eF.symm : (d (rep t)).c₂.F →+* c'.F)) (e j).1))
        (ik : (U (rep t)).Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] ((U (rep t)).X k).Λ)
        (th : ∀ k, ((U (rep t)).X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
        (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
        DictLat (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) e F ik φ th (T.x₀ ((i : ℕ) + 1) (sOv T.toCore c' hle)) ∧
        ∀ h γ : GA D (Wc D i), MarkBy (U (rep t)) (Wc D i) (rank_Wc i) (dict (rep t)) (iotaW T i) F ik φ h γ →
          rdU (U (rep t)) f (dict (rep t) h).1 (dict (rep t) h).2 =
            1 * ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := fun t => by
    obtain ⟨u1, u2, g, e, F, ik, φ, th, v1, v2, v3⟩ := b3 (rep t)
    obtain ⟨f, f1, f2, f3⟩ := v3 (a4 (rep t)) (a6 (rep t)) (xi t)
      (hx2 t _ (d (rep t)).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t)
      (hsup t (le_sup_right (a := (c₀ t).F) (IntermediateField.mem_adjoin_simple_self ℚ _)))
    exact ⟨f, f1, f2, u1, u2, g, e, F, ik, φ, th, v1, v2, f3⟩
  choose f b1 b2 b5 using b4
  refine ⟨d, U, dict, f, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 (rep t), a7 (rep t)⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b5⟩, fun t => (b5 t).2.1⟩
  rw [a2]
  exact halfIs_of_eq R (hrep t) (hH (rep t))

end GlobalTheory.OneCover
end
end

section
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.PinsNormal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levJ_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) : levJ R i t' = levJ R i t := by
  have key : ∀ (Q Q' : Finset (Pl D.host.E)) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), Q = Q' →
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ Lev.Frm.A)) =
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q' (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ' Lev.Frm.A)) := by
    rintro Q _ ξ ξ' rfl
    exact Subgroup.ext fun x => Iff.rfl
  have h := key _ _ (R.xiR t') (R.xiR t) e
  unfold levJ levEnv
  exact congrArg (fun K => (Lev.toAfE (Vc D i) K).comap (finHom (Vc D i)).range.subtype) h

theorem repsR_of_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) {K' : Type} [Field K'] {Cl : Type} [Fintype Cl]
    {h : Cl → GA D (Vc D i)} {bad : ℕ} {J' : Subgroup (Bridge.Gf (Vc D i))}
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    (H : RepsR R i t' h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam vol := by
  unfold RepsR at H ⊢
  rwa [levJ_eq R i e, e] at H

theorem extC_down (R : RealDat D A Ks) (i : Fin D.R.m) {K₁ K₂ : Type} [Field K₁] [Field K₂] (j₁ : D.what₂.LL →+* K₁) (j₂ : D.what₂.LL →+* K₂)
    (σ₁ : K₁ →+* ℂ) (σ₂ : K₂ →+* ℂ) (h₁ : σ₁.comp j₁ = D.what₂.embLL) (h₂ : σ₂.comp j₂ = D.what₂.embLL)
    (hs : Function.Surjective j₁) (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (a₁ : VsV D i K₁ →ₛₗ[σ₁] (R.cV i).W) (a₂ : VsV D i K₂ →ₛₗ[σ₂] (R.cV i).W)
    (H₁ : CoefficientBaseChange R i j₁ σ₁ c0 a₁) (H₂ : CoefficientBaseChange R i j₂ σ₂ c0 a₂) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W)
    (hc : ExtC R i σ₂ a₂ c) : ExtC R i σ₁ a₁ c := by
  intro v v' e
  let ε : K₁ ≃+* D.what₂.LL := (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).symm
  have hε : j₁.comp (ε : K₁ →+* D.what₂.LL) = RingHom.id K₁ := RingHom.ext fun x => (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).apply_symm_apply x
  let u : VsV D i D.what₂.LL := ⟨MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank),
    Formalism.L2.Ker.map_mem_VV _ _ _ v.2⟩
  obtain ⟨w₁, e₁, f₁⟩ := H₁ u
  obtain ⟨w₂, e₂, f₂⟩ := H₂ u
  have hw : w₁ = v := Subtype.ext (by
    rw [e₁]
    change MvPolynomial.map j₁ (MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank)) = _
    rw [MvPolynomial.map_map, hε, MvPolynomial.map_id])
  rw [← hw, f₁, ← f₂]
  refine hc w₂ v' ?_
  rw [e, e₂, MvPolynomial.map_map, h₂, ← hw, e₁, MvPolynomial.map_map, h₁]

theorem exists_normal_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ Normal ℚ c'.F := by
  have := c.fin
  have hle : c.F ≤ IntermediateField.normalClosure ℚ c.F ℂ := IntermediateField.le_normalClosure c.F
  have : IsNormalClosure ℚ c.F (IntermediateField.normalClosure ℚ c.F ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun x => IsAlgClosed.splits _
  exact ⟨⟨IntermediateField.normalClosure ℚ c.F ℂ, inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, IsNormalClosure.normal (F := ℚ) (K := c.F) (L := IntermediateField.normalClosure ℚ c.F ℂ)⟩

set_option maxHeartbeats 4000000 in

theorem exists_pins_normal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O hC hfin hfw hG i hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hL : R.toLevCh.Is A.μ0 := hC.lev
  have hchi : R.grp_chiW := hC.grp.chiW
  have hfam := hC.fam
  have hmodels := hC.models
  have hvP : R.thP_vP := hC.thP.vP
  obtain ⟨hpb, hV, hlev⟩ := GlobalTheory.T.baseTuple_pins_orientation_standardFrame_levelMap D G Pl0 T0 A T R κ v₀ O hL hT i hO
  obtain ⟨gramR, c0R, c0L, htie, hc0O⟩ := hO.2.lift.c0
  haveI : Nonempty T0 := ⟨A.μ0⟩
  let rep : T0 → T0 := fun t => Function.invFun R.Q (R.Q t)
  have hrepQ : ∀ t, R.Q (rep t) = R.Q t := fun t => Function.invFun_eq (f := R.Q) ⟨t, rfl⟩
  have hrepE : ∀ t t' : T0, R.Q t' = R.Q t → rep t' = rep t := fun t t' e => congrArg (Function.invFun R.Q) e
  choose pd l₂ h1 h2 using GlobalTheory.CoverHalf.exists_half_of_laws T.toCore R hT.toLawsM hL hpb hG
  obtain ⟨c₁, hc1a, hc1b, hc1xi, hc⟩ := GlobalTheory.OneCover.exists_covers_rep T R hT hL i (Vc D i).rank pd
    (fun t => GlobalTheory.CoverHalf.coverHalf D (R.Q t)) l₂ h1 h2 rep hrepQ
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i)
    (GlobalTheory.PinnedDataGiven.latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => GlobalTheory.T.exists_numberField_heckeCharacter_sqrtNorm_values D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  obtain ⟨c₃, hc₃, hcurve⟩ := GlobalTheory.CurveField.exists_coeff_curveOver _ T.Q.H T.Q.l c₂ 1 one_pos
  obtain ⟨c', hc', hnorm⟩ := exists_normal_coeff c₃
  have h23 : c₂.F ≤ c'.F := hc₃.trans hc'
  have h3 : c₁.F ≤ c'.F := (le_sup_left.trans hc₂).trans h23
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t =>
    (((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc₂).trans h23
  have hle : T.Q.c.F ≤ c'.F := hc1a.trans h3
  have hLL := hc1b.trans h3
  obtain ⟨d, U, dict, f, xi, -, hcov, hhalf, hxi, hcxi, hmod⟩ := hc c' hle h3
  let dδ : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank := fun t => { d (rep t) with cδ := f t }
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := GlobalTheory.T.exists_coefficientMap_extension_rational_values D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id d
  have hrepR : ∀ t, RepsR R i t (h (rep t)) (bad (rep t)) (J' (rep t)) (Lh (rep t)) (gam (rep t)) (vol (rep t)) :=
    fun t => repsR_of_eq R i (hrepQ t) (hrep (rep t)).1
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad (rep t)) (hbad (rep t)).2.2.2.2
    fun PP hPP => (hrepR t).2.1 PP (Or.inr hPP)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad (rep t)) (B t)).2 fun L cc g d => GlobalTheory.T.law_of_squares_selfDual_splitLattice _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := GlobalTheory.T.exists_harmonicCoefficientMap_at_weights D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.T.exists_adelicSide_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h (rep t)) _ (hrepR t).2.2.1
    (hrepR t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c (O i).lev hlev
  let M : OMDat T.toCore R i T0 id :=
    { c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := (O i).lev, dδ := dδ,
      Cl' := fun t => Cl (rep t), fCl := fun t => fCl (rep t),
      bad := fun t => bad (rep t), Lh := fun t => Lh (rep t), La := fun t => La (rep t), Nc := fun t => Nc (rep t),
      gam := fun t => gam (rep t), vol := fun t => vol (rep t), ep := fun t k => epF t (Lh (rep t) k), B := B,
      epF := epF, io := io, hw := hw, φ := φ,
      w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
      U₂ := fun t => U (rep t), dict₂ := fun t => dict (rep t), xi := xi, thAd := thAd,
      Plc := fun t x => ∃ x₀, Place R i t (h (rep t)) c0' (jVx R i t x₀) x }
  have hMP : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) :=
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
      fun t => ⟨⟨h (rep t), J' (rep t), hrepR t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
      ⟨hact _, hact _⟩, fun t => hbad (rep t), fun t => hcl (rep t), fun t => ⟨fun _ => rfl, hepF t⟩, hio,
      fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩
  refine ⟨M, hMP, rfl, ?_, hnorm, hcurve c' hc', fun t x => h3 (hc1xi t x), fun t t' e => ?_⟩
  · obtain ⟨cM, hcM, -, huM⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP
    obtain ⟨cO, -, -, huO⟩ := GlobalTheory.T.coefficientMap_unique_bijective_complex_extension D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i Unit (fun _ => A.μ0) (O i) hO.2
    have hsurj : Function.Surjective (O i).jL := by
      intro x
      have hx : (x : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hO.1 ▸ x.2
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, Subtype.ext ?_⟩
      have := RingHom.congr_fun hO.2.lift.field y
      exact this.trans hy
    have hsame : ExtC R i (inC (O i).c') (O i).c0' cM :=
      extC_down R i (O i).jL jL (inC (O i).c') (inC c') hO.2.lift.field hjL hsurj (c0L i) (O i).c0' c0' hc0O hc0 cM hcM
    have e0 : cM = _ := huO cM hsame
    intro c
    constructor
    · intro hc'
      rw [huO c hc', ← e0]
      exact hcM
    · intro hc'
      rw [huM c hc']
      exact hsame
  · have er : rep t' = rep t := hrepE t t' e
    have key : ∀ a b : T0, a = b → ∀ (fa : Rul (d a).Xo₂ (d a).c₂) (fb : Rul (d b).Xo₂ (d b).c₂),
        ∃ cx : Rul (d b).Xo₂ (d b).c₂, ({ d a with cδ := fa } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) =
          { ({ d b with cδ := fb } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) with cδ := cx } := by
      rintro a _ rfl fa fb
      exact ⟨fa, rfl⟩
    have keyK : ∀ {β : Type} (g : ∀ a, Cl a → β) (a b : T0) (hab : a = b) (k : Cl a), g b (cast (congrArg Cl hab) k) = g a k := by
      rintro β g a _ rfl k
      rfl
    refine ⟨Equiv.cast (congrArg Cl er.symm), key _ _ er (f t') (f t), congr_arg_heq U er, congr_arg_heq dict er,
      congrArg bad er, congrArg vol er, fun k => ⟨keyK Lh _ _ er.symm k, keyK La _ _ er.symm k, keyK Nc _ _ er.symm k,
      keyK gam _ _ er.symm k⟩⟩

end GlobalTheory.PinsNormal
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normalisedData_normalCoefficientField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  atlas_forward_decl GlobalTheory.PinsNormal.exists_pins_normal
end
