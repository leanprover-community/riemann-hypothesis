import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAveragingProjection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsStrictDom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SatakePowerNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentOfProjectionZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterExistsUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantUnipotentContractionStatement

section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem stab_finiteIndex_of_smooth [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G)
    (hc : IsCompact (K : Set G)) (ρ : Representation ℂ G V) (hs : IsSmooth ρ) (x : V) :
    (stab ρ K x).FiniteIndex := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have ho : IsOpen (stab ρ K x : Set K) :=
    (hs x).preimage continuous_subtype_val
  haveI : Finite (K ⧸ stab ρ K x) := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

private theorem normalCore_stab_le_stab_apply (ρ : Representation ℂ G V) (K : Subgroup G) (x : V) (k : K) :
    (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := by
  intro n hn
  have hc : k⁻¹ * n * k ∈ stab ρ K x := by
    have h1 := (Subgroup.normalCore_normal (stab ρ K x)).conj_mem n hn k⁻¹
    rw [inv_inv] at h1
    exact Subgroup.normalCore_le _ h1
  rw [mem_stab] at hc ⊢
  have he : (n : G) * (k : G) = (k : G) * ((k⁻¹ * n * k : K) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  calc ρ (n : G) (ρ (k : G) x) = ρ ((n : G) * (k : G)) x := by
        rw [map_mul, Module.End.mul_apply]
    _ = ρ (k : G) (ρ ((k⁻¹ * n * k : K) : G) x) := by
        rw [he, map_mul, Module.End.mul_apply]
    _ = ρ (k : G) x := by rw [hc]

theorem avg_translate (ρ : Representation ℂ G V) (K : Subgroup G) {x : V}
    (hx : (stab ρ K x).FiniteIndex) (k : K) : avg ρ K (ρ (k : G) x) = avg ρ K x := by
  haveI := hx
  have hN1 : (stab ρ K x).normalCore ≤ stab ρ K x := Subgroup.normalCore_le _
  have hN2 : (stab ρ K x).normalCore ≤ stab ρ K (ρ (k : G) x) := normalCore_stab_le_stab_apply ρ K x k
  rw [avg_eq ρ K hN2, avg_eq ρ K hN1]
  unfold avgH
  congr 1
  have key : ∀ q : K ⧸ (stab ρ K x).normalCore,
      cv ρ K (stab ρ K x).normalCore (ρ (k : G) x) q =
        cv ρ K (stab ρ K x).normalCore x (q * (QuotientGroup.mk k)) := by
    intro q
    have hq : q * (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore) = QuotientGroup.mk (q.out * k) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hq, cv_mk ρ K hN1]
    simp only [cv, Subgroup.coe_mul, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact finsum_comp_equiv (Equiv.mulRight (QuotientGroup.mk k : K ⧸ (stab ρ K x).normalCore))

end GlobalTheory.CompanionTheory.KAvg

open GlobalTheory.OrbitAvg GlobalTheory.CompanionTheory.KAvg in

theorem GlobalTheory.CompanionTheory.KAvg.kInvForm : PositivityTheory.SphericalProduct.KInvForm := by
  unfold PositivityTheory.SphericalProduct.KInvForm
  intro G _ _ _ K _ hc V _ _ ρ hs v₀ hv₀ hne
  have hfi : ∀ x : V, (stab ρ K x).FiniteIndex := fun x => stab_finiteIndex_of_smooth K hc ρ hs x
  let A : V →ₗ[ℂ] V :=
    { toFun := fun x => avg ρ K x
      map_add' := fun x y => avg_add ρ K (hfi x) (hfi y)
      map_smul' := fun c x => avg_smul ρ K (hfi x) c }
  obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ V, f v₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne ((Module.forall_dual_apply_eq_zero_iff ℂ v₀).mp h)
  have hfix : ∀ l ∈ K, ρ l v₀ = v₀ := by
    intro l hl
    have h' : ∀ h : K, ρ h v₀ = ((1 : K →* ℂˣ) h : ℂ) • v₀ := hv₀
    simpa using h' ⟨l, hl⟩
  refine ⟨((f v₀)⁻¹ • f) ∘ₗ A, ?_, ?_⟩
  · intro k hk
    ext v
    show ((f v₀)⁻¹ • f) (avg ρ K (ρ k v)) = ((f v₀)⁻¹ • f) (avg ρ K v)
    rw [avg_translate ρ K (hfi v) ⟨k, hk⟩]
  · show ((f v₀)⁻¹ • f) (avg ρ K v₀) = 1
    rw [avg_fixed ρ K (hfi v₀) hfix, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf]
end

section
noncomputable section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.SphComp

theorem form_heckeVec_dosetInd {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {K : Subgroup G}
    (hK : IsCommensurated K) (ρ : Representation ℂ G V) {x : V} (hx : x ∈ fixed ρ K)
    (l : Module.Dual ℂ V) (hl : ∀ k ∈ K, l ∘ₗ ρ k = l) (g : G) :
    l (heckeVec ρ K (dosetInd ℂ K g) x) =
      (Nat.card {c : G ⧸ K // (c.out : G) ∈ DoubleCoset.doubleCoset g (K : Set G) K} : ℂ) * l (ρ g x) := by
  classical
  set D := DoubleCoset.doubleCoset g (K : Set G) K with hD
  have hm := Formalism.UG.Final.DosetIndMem G K ℂ g
  have hfin : {c : G ⧸ K | c.out ∈ D}.Finite := by
    refine (Formalism.UG.P.finite_support_cosets hK hm.2).subset ?_
    intro c hc
    have h' : c.out ∈ D := hc
    simp only [Set.mem_setOf_eq, dosetInd]
    rw [Set.indicator_of_mem h']
    simp
  have hterm : ∀ γ ∈ D, l (ρ γ x) = l (ρ g x) := by
    intro γ hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hγ
    have e := LinearMap.congr_fun (hl a ha) (ρ g (ρ b x))
    simp only [LinearMap.comp_apply] at e
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, e, GlobalTheory.LGrp.mem_fixed.1 hx _ hb]
  have e1 : l (heckeVec ρ K (dosetInd ℂ K g) x) =
      ∑ᶠ c : G ⧸ K, l (dosetInd ℂ K g c.out • ρ c.out x) :=
    l.toAddMonoidHom.map_finsum (finite_heckeVec hK hm ρ x)
  have e2 : (fun c : G ⧸ K => l (dosetInd ℂ K g c.out • ρ c.out x)) =
      Set.indicator {c : G ⧸ K | c.out ∈ D} (fun _ => l (ρ g x)) := by
    funext c
    by_cases h : c.out ∈ D
    · have h1 : dosetInd ℂ K g c.out = 1 := by
        simp only [dosetInd]
        rw [Set.indicator_of_mem h]
        simp
      rw [Set.indicator_of_mem (show c ∈ {c : G ⧸ K | c.out ∈ D} from h), h1, one_smul, hterm _ h]
    · have h1 : dosetInd ℂ K g c.out = 0 := by
        simp only [dosetInd]
        exact Set.indicator_of_notMem h _
      rw [Set.indicator_of_notMem (show c ∉ {c : G ⧸ K | c.out ∈ D} from h), h1, zero_smul, map_zero]
  have hc : Nat.card {c : G ⧸ K // c.out ∈ D} = hfin.toFinset.card := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    exact Nat.card_coe_set_eq {c : G ⧸ K | c.out ∈ D}
  rw [e1, e2, ← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hfin, hc]
  simp

theorem sphCompare : PositivityTheory.SphericalProduct.SphCompare := by
  intro L _ _ ϖ σ q n hU V _ _ ρ α v₀ hv l hl g
  have hK := Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n
  have e := congrArg l (hv.2.2 _ (Formalism.UG.Final.DosetIndMem _ (KU σ n) ℂ g))
  rw [map_smul, smul_eq_mul, form_heckeVec_dosetInd hK ρ hv.2.1 l hl g] at e
  exact e

end GlobalTheory.CompanionTheory.SphComp

end
end

section
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

namespace GlobalTheory.CompanionTheory.JacSph

theorem hecke_pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (D : CassData G) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hπ : IsSmooth π) (t : D.T) (ht : D.IsDom t)
    (U : Module.End ℂ (fixed π D.J)) (hU : PositivityTheory.Lbc.IsHeckeOpG π D.J (t : G) U) (r : ℕ) :
    D.IsDom (t ^ r) ∧ PositivityTheory.Lbc.IsHeckeOpG π D.J ((t ^ r : D.T) : G) (U ^ r) := by
  induction r with
  | zero =>
    refine ⟨by simpa using (GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).1, ?_⟩
    intro w l _
    simp
  | succ r ih =>
    rw [pow_succ, pow_succ U]
    exact ⟨(GlobalTheory.CompanionTheory.Cass.isDom_monoid G D).2 _ _ ih.1 ht,
      GlobalTheory.T.casselman_first_property G D V π hπ (t ^ r) t ih.1 ht _ _ ih.2 hU⟩

theorem jacNeU : JacNeU := by
  intro L _ _ _ ϖ σ q n V _ _ ρ α hu hadm _ hsat
  obtain ⟨v₀, hv₀⟩ := hsat.exists_vec
  have hfixK : v₀ ∈ fixed ρ (KU σ n) := hv₀.2.1
  refine ⟨v₀, fun hjac => ?_, fun k hk _ => ?_⟩
  · obtain ⟨D, hJ, hN, hNm, hT⟩ := GlobalTheory.T.iwahori_unipotent_datum L ϖ σ q hu n
    obtain ⟨hKo, hKc, hIK, t₀, ht₀d, ht₀s⟩ := GlobalTheory.CompanionTheory.KUFactsU.kuFacts L ϖ σ q n hu
    have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
      (GlobalTheory.T.dominant_unipotent_contraction L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
    have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
    have hproj0 : D.proj ρ v₀ = 0 := by
      refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [hker]
      exact hjac
    have hJK : ∀ x ∈ D.J, x ∈ KU σ n := fun x hx => hIK (hJ ▸ hx)
    have hfixJ : v₀ ∈ fixed ρ D.J :=
      GlobalTheory.LGrp.mem_fixed.2 fun x hx => GlobalTheory.LGrp.mem_fixed.1 hfixK x (hJK x hx)
    obtain ⟨U, hU, -⟩ := GlobalTheory.T.hecke_character_exists_unique (GU σ n) D.J D.isOpen_J D.isCompact_J V ρ hadm.1 t₀
    obtain ⟨j₀, hj₀⟩ := GlobalTheory.CompanionTheory.Cass.hecke_pow_kills_of_proj_eq_zero (GU σ n) D V ρ hadm.1 _ hstr U hU
      ⟨v₀, hfixJ⟩ hproj0
    obtain ⟨l, hlK, hl1⟩ := GlobalTheory.CompanionTheory.KAvg.kInvForm (GU σ n) (KU σ n) hKo hKc V ρ hadm.1 v₀ hfixK hv₀.1
    obtain ⟨j, hj, hS⟩ := GlobalTheory.T.satake_power_nonvanishing L ϖ σ q n hu α t₀ ht₀d ht₀s j₀
    have hUj : (U ^ j) ⟨v₀, hfixJ⟩ = 0 := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
      rw [add_comm, pow_add, Module.End.mul_apply, hj₀, map_zero]
    have hl0 : l (ρ (t₀ ^ j) v₀) = 0 := by
      have h := (hecke_pow D ρ hadm.1 _ hstr.1 U hU j).2 ⟨v₀, hfixJ⟩ l fun x hx => hlK x (hJK x hx)
      rw [hUj] at h
      simpa using h
    have hc := GlobalTheory.CompanionTheory.SphComp.sphCompare L ϖ σ q n hu V ρ α v₀ hv₀ l hlK (t₀ ^ j)
    rw [hl0, mul_zero, hl1, mul_one] at hc
    exact hS hc.symm
  · rw [GlobalTheory.LGrp.mem_fixed.1 hfixK k hk, sub_self]
    exact Submodule.zero_mem _

end GlobalTheory.CompanionTheory.JacSph
end

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  atlas_forward_decl GlobalTheory.CompanionTheory.JacSph.jacNeU
end
