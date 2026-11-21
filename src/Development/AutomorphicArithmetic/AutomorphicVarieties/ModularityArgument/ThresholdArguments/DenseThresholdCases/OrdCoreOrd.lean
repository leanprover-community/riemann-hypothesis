import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.CoreOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.PartPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeOperatorPreservesPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.OrdJac

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open private cl_mem classical_fixed_by_iwahori cl_gen cl_stab from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
open private pa_fin from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
namespace UpperTheory.V.Z.Ord
private theorem ord_parts {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hH : H.Ax) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A]
    (θ : H.X.I.T →* Aˣ) (ι : Qbar l ≃+* ℂ) {P : ∀ (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), H.PartAltAlt ι lam ξ → Prop}
    (hP : _root_.UpperTheory.V.Z.Ord.AutYAlt H ι P) (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ)
    (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d) (hs : H.IsSpec θ ι x.toRingHom lam ξ c0 sp) (hlam : lam ∈ H.admitted) (K : H.Lev) :
    H.OrdAt θ ι x.toRingHom lam ξ K c0 =
      ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.OrdAt θ ι x.toRingHom lam ξ K c0 := by
  have h1 : H.ClAt θ ι x.toRingHom lam ξ K c0 ≤
      ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y}, Y.1.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    intro F hF
    have hF' := (cl_mem H ι θ _ lam ξ K c0 F).1 hF
    exact _root_.classical_in_iwahori_parts H ι θ _ lam ξ K c0 hH (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y} => Y.1) F hF
      (hP lam hlam d ξ hs.alg F hF'.1 ⟨K, hF'.2.1⟩ ⟨c0, classical_fixed_by_iwahori H ι θ _ lam ξ K c0 c0 le_rfl hs.triv F hF⟩)
  refine le_antisymm (iSup_le fun μ => ?_) (iSup_le fun _ => inf_le_right)
  haveI := hs.fin K c0 le_rfl
  have h2 := cl_gen (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y} => Y.1.Y) (H.ClAt θ ι x.toRingHom lam ξ K c0) (H.uzC ι lam d)
    (cl_stab H ι θ _ lam ξ K c0 c0 le_rfl hs.triv) (fun Y => _root_.classical_parts_commute H ι lam ξ Y.1) h1 μ.1
  have h3 : H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1 ≤ H.OrdAt θ ι x.toRingHom lam ξ K c0 :=
    le_iSup (fun μ : {μ : ℂ // ‖ι.symm μ‖ = 1} =>
      H.ClAt θ ι x.toRingHom lam ξ K c0 ⊓ (H.uzC ι lam d).maxGenEigenspace μ.1) μ
  exact h2.trans (iSup_mono fun Y => inf_le_inf_left _ h3)
set_option maxHeartbeats 800000 in
theorem ordinary_pt_of_literal_automorphy_n : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.PartPtAlt := by
  intro _ L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K _ y hy
  haveI : Finite (ResidueField c.O) := by
    haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (UpperTheory.V.Base.dvrFacts l c.O).2.2.1
    haveI : Finite (ResidueField ℤ_[l]) := IsCNL.finite
    exact Module.finite_of_finite (ResidueField ℤ_[l])
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, hK⟩ := hiComm L Ω l n c H hH A θ hθ K
  haveI := (hK a).2.1
  obtain ⟨e, he, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨-, -, -, -, -, -, h4, -⟩ := pa_fin (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A)
    e he hi hY ι x sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    _ (Submodule.span ℂ (sp '' H.MK θ a K)) (hsp.span K c0 le_rfl) rfl (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam d ξ Y} => Y.1.Y)
    (fun Y => _root_.hecke_operator_preserves_part H ι lam ξ Y.1) (ord_parts H hH θ ι hP x lam d ξ c0 sp hsp hlam K)
  obtain ⟨Y, F, hF0, hF, h⟩ := h4 y hy
  exact ⟨Y.1, F, Y.2, hF0, hF, h⟩
end UpperTheory.V.Z.Ord
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open private UpperTheory.V.Hi.OrdB.inv_inj UpperTheory.V.Hi.OrdB.exists_form UpperTheory.V.Hi.OrdB.num UpperTheory.V.Hi.OrdB.tc_single from Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ExistsNil
theorem UpperTheory.V.Z.Ord.ordinary_jacquet_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → OrdJac := by
  intro H k _ _ _ _ n V _ _ π hπ hirr c φ hφ0 v hv hv0 a ha
  obtain ⟨hker, hsm, hI, -, -, -, -, hidx, hz, hT⟩ := glBridge k n V π
  have hφ : ∀ t : (glIwa k n).T, (t : GL (Fin n) k) ∈ (glIwa k n).Tc c → φ t = 1 := fun t ht => by
    obtain ⟨y, hy, hy'⟩ := hT t
    have e : (t : GL (Fin n) k) ∈ φ.ker.map (glIwa k n).T.subtype := by
      rw [hy]
      refine list_prod_mem fun x hx => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact ⟨eT k n i (y i), hφ0 i _ (hy' c ht i), rfl⟩
    obtain ⟨s, hs, e⟩ := e
    exact (Subtype.ext e : s = t) ▸ hs
  haveI : FiniteDimensional ℂ (fixd π ((glIwa k n).I1 c)) := by
    have hfix : fixd π ((glIwa k n).I1 c) = fixed π ((glIwa k n).I1 c) := by
      ext w
      exact ⟨fun h u => by simpa using h u u.2, fun h u hu => by simpa using h ⟨u, hu⟩⟩
    rw [hfix]
    exact ((H.loc.bz k).1 _ V π hπ hirr).2 _ (hI c).1 (hI c).2
  let p : V →ₗ[ℂ] Jacquet π (unipB k (Fin n)) := Submodule.mkQ _
  have hp : ∀ t w, jacB π t (p w) =
      (((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) t))⁻¹ : ℂˣ) : ℂ) • p (π (diagT k (Fin n) t) w) :=
    fun t w => UnramFixed.jacB_apply π t _
  have hlist : ∀ s : List ℕ, (∀ j ∈ s, j < n) → (s.map (al k n)).prod ∈ (glIwa k n).P ∧
      ∃ b : ℂ, b ≠ 0 ∧ (glIwa k n).uOp π (s.map (al k n)).prod v = b • v := by
    intro s
    induction s with
    | nil =>
      exact fun _ => ⟨one_mem _, 1, one_ne_zero, by
        simpa using (uOpMul _ (glIwa k n) ℂ V π 1 1 (one_mem _) (one_mem _) v hv.1).2.2.1⟩
    | cons j s ih =>
      intro hs
      obtain ⟨hP, b, hb, h2⟩ := ih fun i hi => hs i (List.mem_cons_of_mem _ hi)
      rw [List.map_cons, List.prod_cons]
      refine ⟨mul_mem (al_mem k n j) hP, ?_⟩
      rcases j with _ | j
      · have e : al k n 0 = 1 := by
          rw [al, upow, ← (diagT k (Fin n)).map_one]; congr 1; funext i; simp
        rw [e, one_mul]
        exact ⟨b, hb, h2⟩
      · have hj := ha ⟨j, by have := hs _ List.mem_cons_self; omega⟩
        refine ⟨a (j + 1) * b, mul_ne_zero hj.1 hb, ?_⟩
        rw [← (uOpMul _ (glIwa k n) ℂ V π _ _ (al_mem k n _) hP v hv.1).2.1, h2, map_smul]
        have e := hj.2
        simp only at e
        rw [e, smul_smul, mul_comm]
  obtain ⟨-, b, hb, hzb⟩ := hlist (List.range n) fun j hj => List.mem_range.1 hj
  rw [← hz] at hzb
  have hpow : ∀ j : ℕ, ((glIwa k n).uOp π (glIwa k n).z ^ j) v = b ^ j • v := fun j => by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hzb, smul_smul, pow_succ]
  have hvi : v ∈ invPart π c φ := (Submodule.mem_iInf _).2 fun j =>
    ⟨(b ^ j)⁻¹ • v, Submodule.smul_mem _ _ hv, by
      rw [map_smul, hpow, smul_smul, inv_mul_cancel₀ (pow_ne_zero j hb), one_smul]⟩
  have hx0 : p v ≠ 0 := fun h => hv0 (UpperTheory.V.Hi.OrdB.inv_inj _ π c φ hφ (hsm hπ) hvi
    (hker ▸ (Submodule.Quotient.mk_eq_zero _).1 h))
  have hl : HasFiniteLength (jacB π) :=
    (hasFiniteLength_comp_iff _ _ (leviTorus k (Fin n)).surjective).2
      ((H.loc.bz k).2.1 _ _ _ (points (Fin n)) _ π hπ (hasFiniteLength_of_isIrreducible hirr))
  haveI := GlobalTheory.TorusEigenform.secondCountableTopology_units k
  obtain ⟨μ, hμs, hμ, l, hl0, hle⟩ := UpperTheory.V.Hi.OrdB.exists_form (isSmooth_jacB hπ) hl hx0
  obtain ⟨ψ, hψ, rfl⟩ : ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ torusChar ψ = μ := by
    refine ⟨fun i => μ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
      fun i => hμs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), MonoidHom.ext fun t => ?_⟩
    rw [torusChar_apply]
    conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
    rfl
  have hsq : IsSubquotient π (prinSeries ψ) := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hirr _ l hl0 hle
  have hψφ : ∀ i (u : Uo k), ψ i u = (φ (eT k n i u))⁻¹ := fun i u => by
    have hO : (Pi.mulSingle i (u : kˣ) : Fin n → kˣ) ∈ torusO k (Fin n) := fun j => by
      by_cases h : j = i
      · subst h
        rw [Pi.mulSingle_eq_same]; exact u.2
      · simp [Pi.mulSingle_eq_of_ne h]
    have h1 : jacB π (Pi.mulSingle i (u : kˣ)) (p v) = (((φ (eT k n i u))⁻¹ : ℂˣ) : ℂ) • p v := by
      rw [hp, UnramFixed.deltaHalf_torusO k hO, inv_one, Units.val_one, one_smul, ← map_smul]
      exact congrArg p (hv.2.2 (eT k n i u))
    rw [← UpperTheory.V.Hi.OrdB.tc_single]
    exact Units.ext (hμ _ _ h1)
  obtain ⟨ω, rfl⟩ : ∃ ω : Fin n → kˣ →* ℂˣ, (fun i => ω i * absPow k (((n : ℂ) - 1) / 2)) = ψ :=
    ⟨fun i => ψ i * (absPow k (((n : ℂ) - 1) / 2))⁻¹, funext fun i => inv_mul_cancel_right _ _⟩
  have hω : ∀ i, IsSmoothChar (ω i) := fun i => by
    have := (hψ i).mul (isSmoothChar_of_isUnram (isUnram_absPow k (-(((n : ℂ) - 1) / 2))))
    rwa [absPow_neg, mul_inv_cancel_right] at this
  have hinv : IsInvOn φ ω := fun i u => by
    have := hψφ i u
    rw [MonoidHom.mul_apply, isUnram_absPow k _ _ u.2, mul_one] at this
    rw [this, inv_inv]
  refine ⟨ω, hω, hinv, hsq, fun j => ?_⟩
  have hm : (j : ℕ) + 1 ≤ n := j.2
  have h1 := propCp _ (glIwa k n) ℂ V π _ (al_mem k n ((j : ℕ) + 1)) v hv.1
  rw [hker, hidx _ hm] at h1
  have h2 : p _ = 0 := (Submodule.Quotient.mk_eq_zero _).2 h1
  rw [map_sub, map_smul, sub_eq_zero, (ha j).2, map_smul] at h2
  have hQ : ((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 (pow_ne_zero _ Nat.card_pos.ne')
  have h3 := hμ (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))
    ((((deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n)
      (fun i => UpperTheory.V.Hi.unif k ^ (if (i : ℕ) < (j : ℕ) + 1 then 1 else 0 : ℤ))))⁻¹ : ℂˣ) : ℂ) *
      (((Nat.card 𝓀[k] ^ (((j : ℕ) + 1) * (n - ((j : ℕ) + 1))) : ℕ) : ℂ)⁻¹ * a ((j : ℕ) + 1))) (by
    rw [hp, mul_smul]
    congr 1
    rw [mul_smul, h2, smul_smul, inv_mul_cancel₀ hQ, one_smul]
    rfl)
  have key : ∀ (Q x : ℂ) (d : ℂˣ), Q ≠ 0 → Q * ((d : ℂ) * (((d⁻¹ : ℂˣ) : ℂ) * (Q⁻¹ * x))) = x := fun Q x d h => by
    rw [Units.val_inv_eq_inv_val]
    have := d.ne_zero
    field_simp
  rw [← UpperTheory.V.Hi.OrdB.num ω hm, h3]
  exact key _ _ _ hQ
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem char_at {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M)
    {F : M} (hne : F ≠ 0) (h : ∀ t, ∃ a : ℂ, ρ t F = a • F) :
    ∃ φ : G →* ℂˣ, ∀ t, ρ t F = (((φ t)⁻¹ : ℂˣ) : ℂ) • F := by
  choose a ha using h
  let χ : G →* ℂ :=
    { toFun := a
      map_one' := smul_left_injective ℂ hne (by simpa using (ha 1).symm)
      map_mul' := fun s t => smul_left_injective ℂ hne (by
        have := ha (s * t)
        rw [map_mul, Module.End.mul_apply, ha t, map_smul, ha s, smul_smul, mul_comm] at this
        exact this.symm) }
  exact ⟨χ.toHomUnits⁻¹, fun t => by simpa [χ] using ha t⟩
private theorem uOp_at {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
    {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M) (v : σ) {a : G v} (ha : a ∈ (I v).P) :
    ∀ F ∈ fixd π (piIwa I).N,
      (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hP : Pi.mulSingle v a ∈ (piIwa I).P := fun w _ => by
    rcases eq_or_ne w v with rfl | h
    · simpa using ha
    · simpa [Pi.mulSingle_eq_of_ne h] using (I w).P.one_mem
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := fun u hu => (Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu
  have hc : ∀ {H : Type} [Group H] (J : Iwa H) (b y : H), y ∈ J.Nconj b ↔ b⁻¹ * y * b ∈ J.N := fun J b y =>
    ⟨by rintro ⟨z, hz, rfl⟩; simpa [mul_assoc] using hz, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  intro F hF
  obtain ⟨⟨s, hs, hs'⟩, hsum⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  have key : ∀ y ∈ (piIwa I).N, ∀ u : G v, (Pi.mulSingle v u)⁻¹ * y ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔
      u⁻¹ * y v ∈ (I v).Nconj a := fun y hy u => by
    rw [hc, hc]
    refine ⟨fun h => by simpa using h v trivial, fun h w _ => ?_⟩
    rcases eq_or_ne w v with rfl | e
    · simpa using h
    · simpa [Pi.mulSingle_eq_of_ne e] using hy w trivial
  rw [(hsum s hs hs').2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ hP).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image fun _ _ _ _ e => Pi.mulSingle_injective v e]
  · exact Finset.sum_congr rfl fun u _ => by rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hu
    exact hN w (hs w hw)
  · intro y hy
    obtain ⟨u, ⟨hu, hu'⟩, huq⟩ := hs' (y v) (hy v trivial)
    refine ⟨_, ⟨Finset.mem_image_of_mem _ hu, (key y hy u).2 hu'⟩, ?_⟩
    rintro _ ⟨hw, hw'⟩
    obtain ⟨w, hw₁, rfl⟩ := Finset.mem_image.1 hw
    rw [huq w ⟨hw₁, (key y hy w).1 hw'⟩]
private theorem Uc_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : ℕ} (h : a ≤ b) : Uc k b ≤ Uc k a := by
  refine Subgroup.map_mono fun u hu => ?_
  rw [MonoidHom.mem_ker, Units.ext_iff] at hu ⊢
  exact (Ideal.Quotient.eq (y := 1)).2 (Ideal.pow_le_pow_right h ((Ideal.Quotient.eq (y := 1)).1 hu))
private theorem local_exp (hJ : OrdJac) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (GL (Fin n) k) M) {Y : Submodule ℂ M} (σ : SmIrr (GL (Fin n) k)) (hσ : IsoSum ρ Y σ)
    {F : M} (hFY : F ∈ Y) (hF0 : F ≠ 0) (e : ℕ) (f : Fin n → Uo k → ℂ)
    (hN : F ∈ fixd ρ (glIwa k n).N) (hNm : F ∈ fixd ρ ((glIwa k n).Nm e))
    (hT : ∀ i y, ρ (eT k n i y) F = (f i y)⁻¹ • F)
    (htriv : ∀ i (y : Uo k), (y : kˣ) ∈ Uc k (e + 1) → f i y = 1) (a : ℕ → ℂ)
    (ha : ∀ j : Fin n, a (j + 1) ≠ 0 ∧ (glIwa k n).uOp ρ (al k n (j + 1)) F = a (j + 1) • F) :
    ∃ ω : Fin n → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ω i)) ∧ IsSubquotient σ.ρ (PS ω) ∧
      (∀ i (y : Uo k), (ω i y : ℂ) * f i y = 1) ∧ ∀ j : Fin n, psEig ω (j + 1) = a (j + 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgen⟩ := glBridge k n M ρ
  obtain ⟨φ, hφ⟩ := char_at (ρ.comp (glIwa k n).T.subtype) hF0 fun t => by
    obtain ⟨y, hy, -⟩ := hgen t
    change ∃ a : ℂ, ρ t F = a • F
    rw [hy]
    refine List.prod_induction (fun g => ∃ a : ℂ, ρ g F = a • F) ?_ ⟨1, by simp⟩ ?_
    · rintro g g' ⟨a, ha⟩ ⟨b, hb⟩
      exact ⟨b * a, by rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul]⟩
    · intro g hg
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hg
      exact ⟨_, hT i (y i)⟩
  have hval : ∀ i y, (φ (eT k n i y) : ℂ) = f i y := fun i y => by
    have := smul_left_injective ℂ hF0 ((hφ (eT k n i y)).symm.trans (hT i y))
    rwa [Units.val_inv_eq_inv_val, inv_inj] at this
  obtain ⟨p, hp, hp0⟩ := isoSep hσ hFY hF0
  have hpe : p F ∈ (glIwa k n).eig σ.ρ e φ :=
    ⟨fun u hu => by rw [← hp u F hFY, hN u hu], fun u hu => by rw [← hp u F hFY, hNm u hu],
      fun t => (hp _ F hFY).symm.trans ((congrArg p (hφ t)).trans (map_smul p _ _))⟩
  obtain ⟨ω, h1, h2, h3, h4⟩ := hJ k n σ.V σ.ρ σ.smooth σ.irred e φ
    (fun i y hy => Units.ext (by rw [hval, htriv i y hy, Units.val_one])) (p F) hpe hp0 a fun j =>
      ⟨(ha j).1, (uOpNat _ _ ℂ _ _ ℂ _ σ.ρ p.toAddMonoidHom _ (al_mem k n (j + 1)) F fun u _ => hp _ F hFY).symm.trans
        ((congrArg p (ha j).2).trans (map_smul p _ _))⟩
  exact ⟨ω, h1, h3, fun i y => by rw [← hval, h2 i y, Units.mul_inv], h4⟩
theorem UpperTheory.V.Z.Ord.ordinary_scalar_of_literal_automorphy_n : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.OrdScalAlt := by
  intro hLit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K e he F hF hF0 v b hb
  classical
  have hN : F ∈ fixd (H.atV d v) (glIwa _ n).N := fun u hu =>
    hF.2.1.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hNm : F ∈ fixd (H.atV d v) ((glIwa _ n).Nm e) := fun u hu =>
    hF.2.1.2 _ ((Subgroup.mulSingle_mem_pi _ _).2 fun _ => hu)
  have hT : ∀ i y, H.atV d v (eT _ n i y) F = (ι (H.finPart θ x.toRingHom lam v i y))⁻¹ • F := fun i y => by
    have := hF.2.2
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff] at this
    exact this v i y
  have hop : ∀ j : Fin n, H.opC ι lam d (.inr (v, j)) F =
      (H.lowVal ι lam v (j + 1))⁻¹ • (glIwa _ n).uOp (H.atV d v) (al _ n (j + 1)) F := fun j =>
    congrArg ((H.lowVal ι lam v (j + 1))⁻¹ • ·)
      (uOp_at (fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n) (H.X.rpF ℂ d H.m) v (al_mem _ n (j + 1)) F hF.2.1.1.2)
  have hl : ∀ j : Fin n, H.lowVal ι lam v (j + 1) ≠ 0 := fun j h0 => by
    have := (hb j).2
    rw [hop j, h0, inv_zero, zero_smul] at this
    exact smul_ne_zero (hb j).1 hF0 this.symm
  let a : ℕ → ℂ := fun m => H.lowVal ι lam v m * (if h : m - 1 < n then b ⟨m - 1, h⟩ else 0)
  have ha : ∀ j : Fin n, a (j + 1) = H.lowVal ι lam v (j + 1) * b j := fun j => by
    have h : (j : ℕ) + 1 - 1 < n := by simpa using j.2
    simp only [a, dif_pos h]
    congr 2
  obtain ⟨ω, h1, h2, h3, h4⟩ := local_exp (_root_.UpperTheory.V.Z.Ord.ordinary_jacquet_of_literal_automorphy_n hLit) (H.atV d v) (Y.σl v) (Y.isoL v) hF.1 hF0 e
    (fun i y => ι (H.finPart θ x.toRingHom lam v i y)) hN hNm hT
    (fun i y hy => by rw [hsp.triv v i y (Uc_le _ (by omega) hy), map_one]) a fun j =>
      ⟨by rw [ha j]; exact mul_ne_zero (hl j) (hb j).1, by
        have h := (hop j).symm.trans (hb j).2
        rw [inv_smul_eq_iff₀ (hl j), smul_smul] at h
        rw [ha j]
        exact h⟩
  exact ⟨ω, h1, h2, h3, fun j => by rw [h4 j, ha j, inv_mul_cancel_left₀ (hl j)]⟩
end
end

section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
set_option synthInstance.maxHeartbeats 200000
theorem UpperTheory.V.Z.Ord.core_ordinary_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Z.Ord.CoreOrdAlt := by
  intro hL L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ ι P hP a K _ _ D ψ hU lam hlam y hy
  let x : A →ₐ[c.O] Qbar l := y.comp (IsScalarTower.toAlgHom c.O A (H.TK θ a K))
  have hx : y.toRingHom.comp (algebraMap A _) = x.toRingHom := rfl
  rw [hx] at hy
  obtain ⟨d, ξ, c0, sp, hsp⟩ := UpperTheory.V.Hi.spec L Ω l n c H hA A θ hθ ι x lam hy
  obtain ⟨Y, F, hY, hF0, hF, hop⟩ :=
    _root_.UpperTheory.V.Z.Ord.ordinary_pt_of_literal_automorphy_n hL L Ω l n c H hA A θ hθ ι P hP x lam d ξ c0 sp hsp hlam a K y hx
  obtain ⟨hD, hch⟩ := _root_.UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level hL L Ω l n c H hA A θ hθ ι a K D ψ hU y lam d ξ Y F hF.1 hF0
    fun w j => hop _
  refine ⟨d, ξ, Y, hY, hD, fun v => ?_⟩
  have hle : H.OrdAt θ ι x.toRingHom lam ξ K c0 ≤ H.ClAt θ ι x.toRingHom lam ξ K c0 := by
    unfold HSet.OrdAt
    exact iSup_le fun _ => inf_le_left
  have hC : F ∈ Y.Y ⊓ H.ClAt θ ι x.toRingHom lam ξ K c0 := ⟨hF.1, hle hF.2⟩
  have hne : ∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) ≠ 0 := fun j => by
    obtain ⟨s, hs⟩ := (hA.art_spec v).surj (unif _)
    rw [← hU.ψ_unif v j s (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) s) rfl hs]
    exact (map_ne_zero ι).2 ((Units.isUnit _).map y).ne_zero
  obtain ⟨ω, hsm, hPS, hinv, hb⟩ := _root_.UpperTheory.V.Z.Ord.ordinary_scalar_of_literal_automorphy_n hL L Ω l n c H hA A θ hθ ι x lam d ξ c0 sp hsp
    Y K c0 le_rfl F hC hF0 v (fun j => ι (y (H.gen θ a K (.inr (v, j))))) fun j => ⟨hne j, hop _⟩
  exact ⟨ω, hPS, hch v ω hsm hinv hb⟩
end
end
