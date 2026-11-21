import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHcharPrescribedTrivial
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HilbertClassFieldOfGlobalArtinReciprocity
import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.CyclicCMExtension
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.CMDescent
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.SplitPlaceExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobPolyOfRecTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResGRangeSpec
import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity
import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.ConjugatePlaceNorm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleRestrictNormalFiniteIndex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleOfRestrictNormalFiniteIndex
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.WdRestrict
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialOfCountZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedCharOfCuspidalSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameter
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BernsteinZelevinskyFinitenessHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankEquivariantFunctionalsCongr
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SemisimpleConjOfTraceEqual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilTraceEqOfSameWd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.PRep GlobalTheory.SmGL
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilElementExistence

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem exists_weil_mem {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
    (S : Set (Dec (F := F) A)) (hS : IsOpen S) (d : Dec (F := F) A) (hd : d ∈ S) :
    ∃ τ : Weil h, (⟨τ.1, Weil_le_Dec h τ.2⟩ : Dec (F := F) A) ∈ S := by
  obtain ⟨t, ht, hts⟩ := isOpen_induced_iff.mp hS
  have hdt : (d : G F Ω) ∈ t := by
    rw [← hts] at hd
    exact hd
  have hnhds : {x : G F Ω | (d : G F Ω) * x ∈ t} ∈ nhds (1 : G F Ω) := by
    apply (continuous_const_mul (d : G F Ω)).continuousAt.preimage_mem_nhds
    simpa using ht.mem_nhds hdt
  obtain ⟨L, hL, hLs⟩ := (krullTopology_mem_nhds_one_iff F Ω _).mp hnhds
  let pb := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨τ, hτW, hτ⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup F Ω A w h (d : G F Ω) d.2 (pb.gen : Ω)
  have hfix : (d : G F Ω)⁻¹ * τ ∈ L.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have e : (((d : G F Ω)⁻¹ * τ : G F Ω) : Ω →ₐ[F] Ω).comp L.val = L.val := pb.algHom_ext (by
      show ((d : G F Ω)⁻¹ * τ) (pb.gen : Ω) = pb.gen
      rw [AlgEquiv.mul_apply, hτ]
      show ((d : G F Ω)⁻¹ * (d : G F Ω)) (pb.gen : Ω) = pb.gen
      simp)
    exact congrArg (fun φ : L →ₐ[F] Ω => φ ⟨x, hx⟩) e
  have hτt : τ ∈ t := by
    have := hLs hfix
    simpa using this
  refine ⟨⟨τ, hτW⟩, ?_⟩
  rw [← hts]
  exact hτt

end WeilElementExistence

open WeilElementExistence in
theorem weil_element_exists : K1 := by
  intro F Ω _ _ _ _ _ S _ v A hinj hA χ hχ
  classical
  obtain ⟨art, hart⟩ := GlobalTheory.globalArtinReciprocity_holds F Ω
  have hLA : ∀ s, ∃ a : Weil (hA s) →* ((v s).adicCompletion F)ˣ, IsLocalArtin (hA s) a := fun s =>
    GlobalTheory.localArtinExists_holds F Ω (A s) (v s) (hA s)
  choose a ha using hLA
  have hfin : ∀ s, ∃ N : ℕ, 0 < N ∧ ∀ g, χ s g ^ N = 1 := fun s => by
    have : CompactSpace (Dec (F := F) (A s)) := isCompact_iff_compactSpace.1 (isClosed_Dec (A s)).isCompact
    have : Finite (Dec (F := F) (A s) ⧸ (χ s).ker) := Subgroup.quotient_finite_of_isOpen _ (hχ s)
    refine ⟨(χ s).ker.index, Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite, fun g => ?_⟩
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 ((χ s).ker.pow_index_mem g)
  have hθ : ∀ s, ∃ θ : ((v s).adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧ (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧
      ∀ σ : Weil (hA s), θ (a s σ) = χ s ⟨σ.1, Weil_le_Dec (hA s) σ.2⟩ := fun s => by
    let ξ : Weil (hA s) →* ℂˣ := (χ s).comp (Subgroup.inclusion (Weil_le_Dec (hA s)))
    have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := by
      have hc : Continuous (fun σ : Ine (F := F) (A s) =>
          (⟨σ.1, Ine_le_Dec (A s) σ.2⟩ : Dec (F := F) (A s))) :=
        continuous_subtype_val.subtype_mk _
      exact (hχ s).preimage hc
    obtain ⟨θ, hθs, e⟩ := (ha s).factor ξ hξ
    obtain ⟨N, hN, hN1⟩ := hfin s
    refine ⟨θ, hθs, ⟨N, hN, MonoidHom.ext fun x => ?_⟩, fun σ => (DFunLike.congr_fun e σ).symm⟩
    obtain ⟨σ, rfl⟩ := (ha s).surj x
    have e' : θ (a s σ) = ξ σ := (DFunLike.congr_fun e σ).symm
    show θ (a s σ) ^ N = 1
    rw [e']
    exact hN1 (Subgroup.inclusion (Weil_le_Dec (hA s)) σ)
  choose θs hθs using hθ
  have hex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ θ : (w.adicCompletion F)ˣ →* ℂˣ, IsSmoothChar θ ∧
      (∃ N : ℕ, 0 < N ∧ θ ^ N = 1) ∧ ∀ t (e : v t = w), θ = e ▸ θs t := fun w => by
    by_cases hw : ∃ t, v t = w
    · obtain ⟨t, rfl⟩ := hw
      refine ⟨θs t, (hθs t).1, (hθs t).2.1, fun t' e => ?_⟩
      obtain rfl := hinj e
      rfl
    · exact ⟨1, by unfold IsSmoothChar; simp, ⟨1, one_pos, one_pow 1⟩, fun t e => absurd ⟨t, e⟩ hw⟩
  choose θ' hθ'1 hθ'2 hθ'3 using hex
  have hθ'v : ∀ s, θ' (v s) = θs s := fun s => hθ'3 (v s) s rfl
  obtain ⟨η, ⟨n, hn, hηn⟩, hinf, hloc⟩ := GlobalTheory.DelEps.Twist.exists_hchar_prescribed F (Set.finite_range v).toFinset θ'
    (fun w _ => hθ'1 w) (fun w _ => hθ'2 w)
  have hηloc : ∀ s, η.loc (v s) = θs s := fun s => by
    rw [hloc (v s) (by simp), hθ'v s]
  have h1 : ∀ x, η.1 x ^ n = 1 := fun x => congrArg (fun ξ : HChar F => ξ.1 x) hηn
  have hko : IsOpen (η.1.ker : Set (Ideles F)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow η.1 η.2.1 hn h1
  have hkc : IsClosed (η.1.ker : Set (Ideles F)) := Subgroup.isClosed_of_isOpen _ hko
  have hle : art.ker ≤ η.1.ker := by
    rw [hart.ker]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hkc
    · rintro _ ⟨k, rfl⟩
      exact η.2.2 k
    · rw [GlobalTheory.HeckeGal.infConn, Subgroup.map_le_iff_le_comap]
      intro y hy
      have hinl : Continuous (Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))) :=
        Continuous.units_map _ (continuous_id.prodMk continuous_const)
      have hcl : IsClopen ((Subgroup.comap (Units.map (MonoidHom.inl (InfiniteAdeleRing F)
          (FiniteAdeleRing (𝓞 F) F))) η.1.ker : Subgroup _) : Set (InfiniteAdeleRing F)ˣ) :=
        ⟨hkc.preimage hinl, hko.preimage hinl⟩
      exact hcl.connectedComponent_subset (Subgroup.one_mem _) hy
  let e := QuotientGroup.quotientKerEquivOfSurjective art hart.quot.surjective
  let cη : Gab F Ω →* ℂˣ := (QuotientGroup.lift art.ker η.1 hle).comp e.symm.toMonoidHom
  have hc : ∀ x, cη (art x) = η.1 x := fun x => by
    show QuotientGroup.lift art.ker η.1 hle (e.symm (art x)) = η.1 x
    have : e.symm (art x) = QuotientGroup.mk x := e.symm_apply_eq.mpr rfl
    rw [this]; rfl
  have hcc : Continuous cη := by
    rw [hart.quot.isQuotientMap.continuous_iff]
    have : (cη ∘ art) = η.1 := funext hc
    rw [this]; exact η.2.1
  let ψ : G F Ω →* ℂˣ := cη.comp (GlobalTheory.HeckeGal.toAb F Ω)
  have hψc : Continuous ψ := hcc.comp continuous_quot_mk
  have hψn : ∀ g, ψ g ^ n = 1 := fun g => by
    obtain ⟨x, hx⟩ := hart.quot.surjective (GlobalTheory.HeckeGal.toAb F Ω g)
    show cη _ ^ n = 1
    rw [← hx, hc, h1]
  have hψo : IsOpen (ψ.ker : Set (G F Ω)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow ψ hψc hn hψn
  have hW : ∀ s (σ : Weil (hA s)), ψ σ = χ s ⟨σ.1, Weil_le_Dec (hA s) σ.2⟩ := fun s σ => by
    show cη (GlobalTheory.HeckeGal.toAb F Ω σ) = _
    rw [← (ha s).glob art hart σ, hc, ← (hθs s).2.2 σ, ← hηloc s]
    rfl
  have hD : ∀ s (g : Dec (F := F) (A s)), ψ g = χ s g := fun s g => by
    let K : Subgroup (Dec (F := F) (A s)) := (χ s).ker ⊓ (ψ.comp (Dec (F := F) (A s)).subtype).ker
    have hK : IsOpen (K : Set (Dec (F := F) (A s))) :=
      (hχ s).inter (hψo.preimage continuous_subtype_val)
    obtain ⟨τ, hτ⟩ := exists_weil_mem (hA s) ((fun x => g⁻¹ * x) ⁻¹' (K : Set (Dec (F := F) (A s))))
      (hK.preimage (continuous_const.mul continuous_id)) g (by
        show g⁻¹ * g ∈ K
        rw [inv_mul_cancel]
        exact K.one_mem)
    have hτ' : g⁻¹ * (⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ : Dec (F := F) (A s)) ∈ K := hτ
    obtain ⟨k1, k2⟩ := Subgroup.mem_inf.1 hτ'
    have e1 : χ s g = χ s ⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ :=
      inv_mul_eq_one.1 (by rw [← map_inv, ← map_mul]; exact MonoidHom.mem_ker.1 k1)
    have e2 : (ψ.comp (Dec (F := F) (A s)).subtype) g =
        (ψ.comp (Dec (F := F) (A s)).subtype) ⟨τ.1, Weil_le_Dec (hA s) τ.2⟩ :=
      inv_mul_eq_one.1 (by rw [← map_inv, ← map_mul]; exact MonoidHom.mem_ker.1 k2)
    have e3 : ψ g = ψ τ := e2
    rw [e3, hW s τ, e1]
  refine ⟨ψ, hψo, hD, fun u _ c hcu => ?_⟩
  obtain ⟨j, hj, hju⟩ := hcu
  have e1 := GlobalTheory.HilbertFromArtin.art_sign_eq hart j c hj
  rw [hju] at e1
  show cη (GlobalTheory.HeckeGal.toAb F Ω c) = 1
  rw [← e1, hc]
  exact DFunLike.congr_fun (hinf u) (-1)

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace PositivityTheory.Pf1.CLGD.K

namespace SupremumMembership

theorem exists_mem_of_sup {Γ : Type*} [Group Γ] (H N : Subgroup Γ) [N.Normal] (hHN : H ⊔ N = ⊤)
    (H₁ H₂ : Subgroup Γ) (h1 : H ≤ H₁) (h12 : H₁ < H₂) : ∃ n ∈ H₂, n ∉ H₁ ∧ n ∈ N := by
  obtain ⟨g, hg2, hg1⟩ := SetLike.exists_of_lt h12
  have hg : g ∈ ((H ⊔ N : Subgroup Γ) : Set Γ) := by rw [hHN]; exact Subgroup.mem_top g
  rw [Subgroup.mul_normal H N] at hg
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hg
  have hx1 : x ∈ H₁ := h1 hx
  refine ⟨y, ?_, ?_, hy⟩
  · have : y = x⁻¹ * (x * y) := by group
    rw [this]
    exact H₂.mul_mem (H₂.inv_mem (h12.le hx1)) hg2
  · intro hy1
    exact hg1 (H₁.mul_mem hx1 hy1)

end SupremumMembership

open SupremumMembership in
theorem place_membership_of_sup : KillingPolyConst := by
  intro E Ω _ _ _ _ _ l a _ ha r hr
  have hcont : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    (Units.continuous_val.comp hr).matrix_trace
  set U : Set (G E Ω) := {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne.preimage hcont
  have h1U : (1 : G E Ω) ∈ U := by
    show (r 1 : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0
    rw [map_one, Units.val_one, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp ha)
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1U
  have : N.toSubgroup.Normal := N.isNormal'
  refine ⟨N.toSubgroup, N.isNormal', N.isOpen', fun H hHN H₁ H₂ h1 h12 => ?_⟩
  obtain ⟨n, hn2, hn1, hnN⟩ := exists_mem_of_sup H N.toSubgroup hHN H₁ H₂ h1 h12
  exact ⟨n, hn2, hn1, hN hnN⟩

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace FrobeniusTraceNorm

theorem sum_eq_zero_of_map_mul {B : Multiset ℂˣ} {ζ : ℂˣ} (hζ : ζ ≠ 1) (h : B.map (· * ζ) = B) :
    (B.map fun b : ℂˣ => (b : ℂ)).sum = 0 := by
  have e : (B.map fun b : ℂˣ => (b : ℂ)).sum = (B.map fun b : ℂˣ => (b : ℂ)).sum * (ζ : ℂ) := by
    conv_lhs => rw [← h]
    rw [Multiset.map_map]
    simp only [Function.comp_def, Units.val_mul]
    exact Multiset.sum_map_mul_right
  have hz : (ζ : ℂ) ≠ 1 := fun e => hζ (Units.ext e)
  have h2 : (B.map fun b : ℂˣ => (b : ℂ)).sum * ((ζ : ℂ) - 1) = 0 := by
    rw [mul_sub, mul_one, ← e, sub_self]
  exact (mul_eq_zero.1 h2).resolve_right (sub_ne_zero.2 hz)

theorem trace_eq_zero_of_frobPoly {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {m : ℕ} (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin m) (Qbar l)) (q : ℕ) (s : Multiset ℂ) (hs : Multiset.card s = m) (h0 : s.sum = 0)
    (h : M.charpoly.map (ι : Qbar l →+* ℂ) = GlobalTheory.SphPar.frobPoly q m s) : M.trace = 0 := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin]
  have e2 : (s.map fun a => X - C (a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ))) =
      ((s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)).map fun x => X - C x) := by
    rw [Multiset.map_map]; rfl
  have hcard : Multiset.card (s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)) = m := by
    rw [Multiset.card_map, hs]
  have e1 : (ι : Qbar l →+* ℂ) (M.charpoly.coeff (m - 1)) = 0 := by
    rw [← Polynomial.coeff_map, h, GlobalTheory.SphPar.frobPoly, e2]
    have key := Polynomial.multiset_prod_X_sub_C_coeff_card_pred
      (s.map fun a => a * (((q : ℝ) ^ (((m : ℝ) - 1) / 2) : ℝ) : ℂ)) (by rw [hcard]; omega)
    rw [hcard] at key
    rw [key, Multiset.sum_map_mul_right, Multiset.map_id', h0, zero_mul, neg_zero]
  have e3 : M.charpoly.coeff (m - 1) = 0 := by
    have : ι (M.charpoly.coeff (m - 1)) = ι 0 := by rw [map_zero]; exact e1
    exact ι.injective this
  rw [e3, neg_zero]

theorem trace_frob_inv_eq_zero (HL : GlobalTheory.Published.LocalLanglandsGL) {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {l : ℕ} [Fact l.Prime]
    {ι : Qbar l ≃+* ℂ} {χ : HChar (maximalRealSubfield E)} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL w (π.locRep w) B)
    (h0 : (B.map fun b : ℂˣ => (b : ℂ)).sum = 0) {A : ValuationSubring Ω} (hA : IsPlaceOver A w) {g : G E Ω}
    (hg : IsFrob (F := E) A (normV w) g) :
    ((r g⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0 := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π w
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π hB hσ
  have hrc := ParLaws.isRec_locRec HL hA
  have e := GlobalTheory.frobPoly_of_rec_twist hA hl ι H.cont hrc (σ := ParLaws.toRep σ) hα (H.wdOf_eq hl hrc hσ) hg
  exact trace_eq_zero_of_frobPoly ι ha _ _ _ (by simp) h0 e

theorem map_mul_eq {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} {π : CuspSub E a} {η : HChar E}
    (hI : (π.twist η).Iso π) {w : HeightOneSpectrum (𝓞 E)} (hu : η.UnrAt w) {B : Multiset ℂˣ}
    (hB : GlobalTheory.LFun.HasSatGL w (π.locRep w) B) : B.map (· * η.val w) = B :=
  (CuspSub.Iso.hasSatGL hI (GlobalTheory.SphGal.hasSatGL_twist E a π η w B hu hB)).unique hB

theorem finite_under {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    {R : Set (HeightOneSpectrum (𝓞 E))} (hR : R.Finite) :
    {w : HeightOneSpectrum (𝓞 M) | w.under (𝓞 E) ∈ R}.Finite := by
  refine (hR.biUnion fun v _ => Ideal.finite_factors (I := Ideal.map (algebraMap (𝓞 E) (𝓞 M)) v.asIdeal)
    (Ideal.map_ne_bot_of_ne_bot v.ne_bot)).subset ?_
  intro w hw
  refine Set.mem_biUnion hw ?_
  show w.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  exact le_rfl

theorem finite_dvd (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] :
    {v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hl : ((l : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 E)})
    (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])).subset ?_
  intro v hv
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem isPlaceOver_under {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 M)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 E)) := by
  intro x
  have e : algebraMap M Ω ((algebraMap (𝓞 E) (𝓞 M) x : 𝓞 M) : M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E M Ω]
    rfl
  rw [← e, h]
  rfl

theorem normV_eq_absNorm {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    normV v = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rfl

theorem isFrob_resG {E M Ω : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Field Ω] [Algebra E M]
    [Algebra E Ω] [Algebra M Ω] [IsScalarTower E M Ω] {A : ValuationSubring Ω} {q : ℕ} {σ : G M Ω}
    (h : IsFrob (F := M) A q σ) : IsFrob (F := E) A q (resG E σ) :=
  ⟨resG_mem_Dec (A := A) h.1, fun x hx => h.2 x hx⟩

end FrobeniusTraceNorm

open FrobeniusTraceNorm in
theorem frobenius_trace_place_norm : ContinuationThroughChart := by
  intro HL E Ω _ _ _ _ _ _ a ha π X hGal hp l _ ι r wt HT H η hη1 hηp hsplit hI g hg

  obtain ⟨art, hart, hfull⟩ := GlobalTheory.Published.HeckeLAdicCharacter.full PositivityTheory.Stage1.PM.heckeLAdicCharacter E Ω
  obtain ⟨-, hex, huniq⟩ := hfull l ι
  obtain ⟨ψ, ⟨hψc, -, hψ⟩, -⟩ := hex _ hp.pos η hηp
  have hψ1 : ψ ≠ 1 := by
    rintro rfl
    have hc1 : Continuous (1 : G E Ω →* (Qbar l)ˣ) := continuous_const
    obtain ⟨χ0, -, hχ0⟩ := huniq _ hp.pos 1 hc1 (one_pow _)
    have e1 := hχ0 η ⟨hηp, hψ⟩
    have e2 := hχ0 1 ⟨one_pow _, fun x σ _ => by simp [infPow_zero, lPow_zero]⟩
    exact hη1 (e1.trans e2.symm)

  have hψM : ∀ τ : G X.M Ω, ψ (resG E τ) = 1 := by
    have hT := Filter.eventually_cofinite.1 hsplit
    have hRM := finite_under (M := X.M) (GlobalTheory.Mem.UnrAe.finite_ramified η)
    have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := X.M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
      (hT.union hRM)
    have hcl : IsClosed ((fun τ : G X.M Ω => ψ (resG E τ)) ⁻¹' {1}) :=
      isClosed_singleton.preimage (hψc.comp continuous_resG)
    intro τ
    refine closure_minimal ?_ hcl (hD τ)
    rintro σ ⟨w, hw, hdeg, B, hB, hF⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hw
    obtain ⟨hwT, hwR⟩ := hw
    have hBv := isPlaceOver_under (E := E) hB
    obtain ⟨f, hf⟩ := exists_normV_pow hBv hB
    have hpr : (normV w).Prime := by
      rw [normV_eq_absNorm]
      exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified X.M).1 w).2 hdeg
    have hf1 : f = 1 := by
      rw [hf] at hpr
      exact hpr.eq_one_of_pow
    subst hf1
    have hv1 : η.val (w.under (𝓞 E)) = 1 := by
      simpa using hwT 1 hf
    have hFv : IsFrob (F := E) B (normV (w.under (𝓞 E))) (resG E σ) := by
      rw [hf, pow_one] at hF
      exact isFrob_resG hF
    have e := hψ.frob_unr hart (Or.inr rfl) hwR hBv hFv
    rw [hv1] at e
    show ψ (resG E σ) = 1
    exact Units.ext (by rw [e]; simp)

  obtain ⟨-, -, -, hopen, hidx, -⟩ := GlobalTheory.DelGlob.resG_range_spec Ω E X.M
  have hidx' : (resG E (E' := X.M) (Ω := Ω)).range.index = Module.finrank E X.M := hidx
  have hopen' : IsOpen ((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω)) := hopen
  have hker : (resG E (E' := X.M) (Ω := Ω)).range ≤ ψ.ker := by
    rintro _ ⟨τ, rfl⟩
    exact hψM τ
  have hne : ∀ g, g ∉ (resG E (E' := X.M) (Ω := Ω)).range → ψ g ≠ 1 := by
    intro g hg h1
    have hdvd : ψ.ker.index ∣ Module.finrank E X.M := hidx' ▸ Subgroup.index_dvd_of_le hker
    rcases (Nat.dvd_prime hp).1 hdvd with h | h
    · apply hψ1
      have hk := Subgroup.index_eq_one.1 h
      refine MonoidHom.ext fun x => ?_
      have : x ∈ ψ.ker := by rw [hk]; exact Subgroup.mem_top x
      simpa using this
    · have hrel := Subgroup.relIndex_mul_index hker
      rw [h, hidx'] at hrel
      have h1' : (resG E (E' := X.M) (Ω := Ω)).range.relIndex ψ.ker = 1 :=
        Nat.eq_of_mul_eq_mul_right hp.pos (hrel.trans (one_mul _).symm)
      exact hg (Subgroup.relIndex_eq_one.1 h1' (MonoidHom.mem_ker.2 h1))

  have hcont : Continuous fun x : G E Ω => ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace :=
    ((Units.continuous_val.comp H.cont).comp continuous_inv).matrix_trace
  have hZ : IsClosed {x : G E Ω | ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0} :=
    isClosed_eq hcont continuous_const
  have hS : ({v : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ v.asIdeal} ∪ {v | ¬ η.UnrAt v} ∪
      {v | ¬ ∃ C, GlobalTheory.LFun.HasSatGL v (π.locRep v) C}).Finite :=
    ((finite_dvd E l).union (GlobalTheory.Mem.UnrAe.finite_ramified η)).union
      (Filter.eventually_cofinite.1 (UnrSat.eventually_hasSatGL_locRep CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π))
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := E) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne' hS
  have hU : IsOpen (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) :=
    (Subgroup.isClosed_of_isOpen _ hopen').isOpen_compl
  have hsub : (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) ⊆
      {x : G E Ω | ((r x⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0} := by
    refine (hD.open_subset_closure_inter hU).trans (closure_minimal ?_ hZ)
    rintro σ ⟨hσM, v, hv, -, B, hB, hF⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hv
    obtain ⟨⟨hl, hu⟩, ⟨C, hC⟩⟩ := hv
    have hψσ := hne σ hσM
    have e := hψ.frob_unr hart (Or.inr rfl) hu hB hF
    have hval : η.val v ≠ 1 := by
      intro h1
      apply hψσ
      refine Units.ext ?_
      rw [e, h1]
      simp
    have h0 := sum_eq_zero_of_map_mul hval (map_mul_eq hI hu hC)
    exact trace_frob_inv_eq_zero HL ha H hl hC h0 hB hF
  have hgi : g⁻¹ ∈ (((resG E (E' := X.M) (Ω := Ω)).range : Set (G E Ω))ᶜ) := fun h =>
    hg (by simpa using (resG E (E' := X.M) (Ω := Ω)).range.inv_mem h)
  have := hsub hgi
  simpa using this

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal
  Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace LocalParameterTwist

section SS

variable {k : Type} [Field k] {a : ℕ}

theorem isInv_iff_of_image {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (ρ₁ : Γ₁ →* GL (Fin a) k)
    (ρ₂ : Γ₂ →* GL (Fin a) k) (h₁₂ : ∀ g, ∃ g', ρ₂ g' = ρ₁ g) (h₂₁ : ∀ g', ∃ g, ρ₁ g = ρ₂ g')
    (W : Submodule k (Fin a → k)) : IsInv ρ₁ W ↔ IsInv ρ₂ W := by
  constructor
  · intro hW g v hv
    obtain ⟨g₁, e⟩ := h₂₁ g
    rw [← e]
    exact hW g₁ v hv
  · intro hW g v hv
    obtain ⟨g₂, e⟩ := h₁₂ g
    rw [← e]
    exact hW g₂ v hv

theorem isSSRep_of_image {Γ₁ Γ₂ : Type} [Group Γ₁] [Group Γ₂] (ρ₁ : Γ₁ →* GL (Fin a) k)
    (ρ₂ : Γ₂ →* GL (Fin a) k) (h₁₂ : ∀ g, ∃ g', ρ₂ g' = ρ₁ g) (h₂₁ : ∀ g', ∃ g, ρ₁ g = ρ₂ g')
    (h : IsSSRep ρ₁) : IsSSRep ρ₂ := by
  intro W hW
  obtain ⟨W', h1, h2⟩ := h W ((isInv_iff_of_image ρ₁ ρ₂ h₁₂ h₂₁ W).2 hW)
  exact ⟨W', (isInv_iff_of_image ρ₁ ρ₂ h₁₂ h₂₁ W').1 h1, h2⟩

theorem isSSRep_comp_subtype [CharZero k] {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin a) k) (H : Subgroup Γ)
    [H.FiniteIndex] (hρ : IsSSRep ρ) : IsSSRep (ρ.comp H.subtype) := by
  have h1 := GlobalTheory.TraceSemisimple.isSSRep_comp_subtype_of_normal_finiteIndex Γ k a ρ H.normalCore
    H.normalCore_normal inferInstance hρ
  refine GlobalTheory.ssRep_of_normal_finiteIndex H k a (ρ.comp H.subtype) (H.normalCore.subgroupOf H)
    (H.normalCore_normal.subgroupOf H) inferInstance (isSSRep_of_image _ _ ?_ ?_ h1)
  · intro n
    exact ⟨⟨⟨n.1, H.normalCore_le n.2⟩, Subgroup.mem_subgroupOf.2 n.2⟩, rfl⟩
  · intro n
    exact ⟨⟨n.1.1, Subgroup.mem_subgroupOf.1 n.2⟩, rfl⟩

end SS

section Range

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem range_resG (X : CMExt E Ω) :
    (resG E (E' := X.M) (Ω := Ω)).range = (IsScalarTower.toAlgHom E X.M Ω).fieldRange.fixingSubgroup := by
  ext σ
  rw [MonoidHom.mem_range, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    obtain ⟨m, rfl⟩ := (AlgHom.mem_fieldRange).1 hx
    show τ (algebraMap X.M Ω m) = algebraMap X.M Ω m
    exact τ.commutes m
  · intro hσ
    refine ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun m => hσ (algebraMap X.M Ω m) ((AlgHom.mem_fieldRange).2 ⟨m, rfl⟩)), ?_⟩
    ext x
    rfl

theorem finiteIndex_range_resG (X : CMExt E Ω) : (resG E (E' := X.M) (Ω := Ω)).range.FiniteIndex := by
  have : IsGalois E Ω := {}
  rw [range_resG]
  set L := (IsScalarTower.toAlgHom E X.M Ω).fieldRange with hL
  have hfd : FiniteDimensional E L := by
    let g : X.M →ₗ[E] L :=
      { toFun := fun m => ⟨algebraMap X.M Ω m, (AlgHom.mem_fieldRange).2 ⟨m, rfl⟩⟩
        map_add' := fun x y => Subtype.ext (map_add (algebraMap X.M Ω) x y)
        map_smul' := fun c x => Subtype.ext (by
          simp [Algebra.smul_def, IsScalarTower.algebraMap_apply E X.M Ω]) }
    refine Module.Finite.of_surjective g fun y => ?_
    obtain ⟨m, hm⟩ := (AlgHom.mem_fieldRange).1 y.2
    exact ⟨m, Subtype.ext hm⟩
  exact ⟨fun h0 => (Module.finrank_pos (R := E) (M := L)).ne'
    ((IntermediateField.finrank_eq_fixingSubgroup_index (F := E) (E' := Ω) L).trans h0)⟩

end Range

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem isPlaceOver_under (X : CMExt E Ω) {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 X.M)}
    (h' : IsPlaceOver A w') : IsPlaceOver A (w'.under (𝓞 E)) := by
  intro x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, ← h' (algebraMap (𝓞 E) (𝓞 X.M) x)]
  have e : algebraMap X.M Ω ((algebraMap (𝓞 E) (𝓞 X.M) x : 𝓞 X.M) : X.M) = algebraMap E Ω (x : E) := by
    rw [IsScalarTower.algebraMap_apply E X.M Ω]
    rfl
  rw [e]

omit [NumberField E] [IsAlgClosure E Ω] in

theorem natCast_notMem_under (X : CMExt E Ω) {w' : HeightOneSpectrum (𝓞 X.M)} {l : ℕ}
    (hl : ((l : ℕ) : 𝓞 X.M) ∉ w'.asIdeal) : ((l : ℕ) : 𝓞 E) ∉ (w'.under (𝓞 E)).asIdeal := by
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hl

theorem charPol_locPar_tw (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra K Ω] [IsAlgClosure K Ω] {a : ℕ} (π : CuspSub K a) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)}
    (h : IsPlaceOver A w) {B : Multiset ℂˣ} (hB : (CG.mk π).HasSat w B) (s : ℝ) (σ : Weil h) :
    ((ParLaws.locPar hL (CG.mk π) h).lpTw s).charPol σ =
      (B.map fun b : ℂˣ => X - C ((((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ deg σ * ((b⁻¹ : ℂˣ) : ℂ) ^ deg σ)).prod := by
  obtain ⟨σ₀, hσ₀, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K a π w
  obtain ⟨α, rfl, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π hB hσ₀
  have hα' : GlobalTheory.SmGL.HasSatake (ParLaws.toRep σ₀).ρ α := hα
  rw [ParLaws.locPar_mk hL hσ₀ h, ParLaws.rec_eq_diag (ParLaws.isRec_locRec hL h) hα', WD.lpTw_mk,
    WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ]
  have e2 : ∀ (c : ℂ) (d : Fin a → ℂ), c • diagEnd d = diagEnd fun i => c * d i := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [mul_assoc]
  rw [e2, charpoly_diagEnd, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

theorem wdOf_eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Type} [Field K] [NumberField K] [IsCMField K]
    [Algebra K Ω] [IsAlgClosure K Ω] {a : ℕ} {π : CuspSub K a} {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield K)} {r : G K Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι r wt HT) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A w)
    (hl : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL K a π w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm

theorem scal_eq (q f : ℕ) (s : ℝ) (d : ℤ) (b : ℂˣ) :
    ((((q ^ f : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) ^ d * (((b ^ f)⁻¹ : ℂˣ) : ℂ) ^ d) =
      (((q : ℂ) ^ ((s : ℝ) : ℂ)) ^ ((f : ℤ) * d) * ((b⁻¹ : ℂˣ) : ℂ) ^ ((f : ℤ) * d)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have h1 : (((q ^ f : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)) = ((q : ℂ) ^ ((s : ℝ) : ℂ)) ^ f := by
    have e0 : ((q ^ f : ℕ) : ℂ) = (((q : ℝ) ^ f : ℝ) : ℂ) := by push_cast; ring
    rw [e0, ← Complex.ofReal_cpow (pow_nonneg hq f), ← Real.rpow_natCast_mul hq, mul_comm,
      Real.rpow_mul_natCast hq, Complex.ofReal_pow, Complex.ofReal_cpow hq, Complex.ofReal_natCast]
  have h2 : (((b ^ f)⁻¹ : ℂˣ) : ℂ) = ((b⁻¹ : ℂˣ) : ℂ) ^ f := by
    rw [← inv_pow, Units.val_pow_eq_pow_val]
  rw [h1, h2, ← zpow_natCast ((q : ℂ) ^ ((s : ℝ) : ℂ)), ← zpow_natCast ((b⁻¹ : ℂˣ) : ℂ), ← zpow_mul, ← zpow_mul]

theorem charpoly_eq_at (hL : GlobalTheory.Published.LocalLanglandsGL) [IsCMField E] (X : CMExt E Ω) {a : ℕ} {π : CuspSub E a}
    {P : CuspSub X.M a} {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} {r' : G X.M Ω →* GL (Fin a) (Qbar l)} {wt' : ℤ}
    {HT' : (X.M →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π (quadChar E ^ a) ι r wt HT)
    (H' : IsGalRepOf P (quadChar X.M ^ a) ι r' wt' HT') {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 X.M)}
    (h' : IsPlaceOver A w') (hl' : ((l : ℕ) : 𝓞 X.M) ∉ w'.asIdeal)
    (hW : ∀ f : ℕ, normV w' = normV (w'.under (𝓞 E)) ^ f →
      ∃ B, (CG.mk π).HasSat (w'.under (𝓞 E)) B ∧ (CG.mk P).HasSat w' (B.map (· ^ f)))
    (σ : Weil h') :
    ((r' σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
      ((r (resG E (σ : G X.M Ω)) : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := by
  have h := isPlaceOver_under X h'
  have hl := natCast_notMem_under X hl'
  obtain ⟨B, hB, hB'⟩ := hW (resF h h') (normV_eq_pow_resF h h')
  refine Polynomial.map_injective ι.toRingHom ι.injective ?_
  have e1 := charPol_wdOf hl' ι (Units.continuous_val.comp H'.cont) σ
  have e2 := charPol_wdOf hl ι (Units.continuous_val.comp H.cont) (resW h h' σ)
  rw [coe_resW] at e2
  rw [← e1, ← e2, wdOf_eq_locPar hL H' h' hl', wdOf_eq_locPar hL H h hl,
    charPol_locPar_tw hL P h' hB', charPol_locPar_tw hL π h hB, deg_resW, normV_eq_pow_resF h h',
    Multiset.map_map]
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [scal_eq]

end Local

end LocalParameterTwist

open LocalParameterTwist in

theorem weak_lift_galois_restriction : FinitePlaceStep := by
  intro hL E Ω _ _ _ _ _ _ a ha π X P hWL l _ ι r wt HT r' wt' HT' H H'
  have hss : IsSSRep (r.comp (resG E (E' := X.M) (Ω := Ω))) := by
    have := finiteIndex_range_resG X
    refine isSSRep_of_image (r.comp (resG E (E' := X.M) (Ω := Ω)).range.subtype) _ ?_ ?_
      (isSSRep_comp_subtype r _ H.ss)
    · rintro ⟨g, g', e⟩
      exact ⟨g', by simp [e]⟩
    · intro g'
      exact ⟨⟨resG E g', g', rfl⟩, rfl⟩
  have hWL' : ∀ᶠ w' : HeightOneSpectrum (𝓞 X.M) in Filter.cofinite, ∀ f : ℕ,
      normV w' = normV (w'.under (𝓞 E)) ^ f →
        ∃ B, (CG.mk π).HasSat (w'.under (𝓞 E)) B ∧ (CG.mk P).HasSat w' (B.map (· ^ f)) := hWL
  have hev := (GlobalTheory.HeightCounting.eventually_natCast_notMem X.M l).and hWL'
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := X.M) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (Filter.eventually_cofinite.1 hev)
  have hall := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G X.M Ω) (Qbar l) a
    (fun g => ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (fun g => ((r (resG E g) : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) _ hD
    (Units.continuous_val.comp H'.cont) ((Units.continuous_val.comp H.cont).comp continuous_resG) (by
      rintro g ⟨v, hv, -, B, hB, hg⟩
      have hv' := not_not.1 hv
      exact charpoly_eq_at hL X ι H H' hB hv'.1 hv'.2 ⟨g, mem_Weil_of_isFrob hB hg⟩)
  obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix (r.comp (resG E (E' := X.M) (Ω := Ω))) r' hss H'.ss
    fun g => (hall g).symm
  exact ⟨Pm⁻¹, fun g => by rw [hPm g, inv_inv]; rfl⟩

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent
open GlobalTheory.WeilDeligne PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

namespace PositivityTheory.Pf1.CLGD.K

namespace WeilDeligneRestriction

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω}

theorem mem_Dec_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Dec (F := E) A) : σ ∈ Dec (F := E') A := by
  have h1 : resG E σ • A = A := hσ
  show σ • A = A
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  conv_rhs => rw [← h1]
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  rfl

theorem mem_Ine_of_resG {σ : G E' Ω} (hσ : resG E σ ∈ Ine (F := E) A) : σ ∈ Ine (F := E') A :=
  ⟨mem_Dec_of_resG hσ.1, fun x hx => hσ.2 x hx⟩

variable (E A) in

def resIne : Ine (F := E') A →* Ine (F := E) A where
  toFun σ := ⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩
  map_one' := Subtype.ext (map_one (resG E))
  map_mul' σ τ := Subtype.ext (map_mul (resG E) (σ : G E' Ω) τ)

@[simp] theorem coe_resIne (σ : Ine (F := E') A) : ((resIne E A σ : Ine (F := E) A) : G E Ω) = resG E (σ : G E' Ω) :=
  rfl

theorem continuous_resIne : Continuous (resIne E A : Ine (F := E') A → Ine (F := E) A) := by
  show Continuous fun σ : Ine (F := E') A => (⟨resG E (σ : G E' Ω), resG_mem_Ine σ.2⟩ : Ine (F := E) A)
  exact ((continuous_resG (E := E) (E' := E') (Ω := Ω)).comp continuous_subtype_val).subtype_mk _

theorem exists_tval_resIne_ne {l : ℕ} [Fact l.Prime] {t : Ine (F := E) A →* Multiplicative ℤ_[l]} (ht : IsTameChar t) :
    ∃ σ : Ine (F := E') A, tval t (resIne E A σ) ≠ 0 := by
  classical
  let bQ := Module.finBasis ℚ E'
  let K : IntermediateField E Ω := IntermediateField.adjoin E (Set.range fun i => algebraMap E' Ω (bQ i))
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : FiniteDimensional E K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let U : Subgroup (Ine (F := E) A) := K.fixingSubgroup.comap (Ine (F := E) A).subtype
  have hU : IsOpen (U : Set (Ine (F := E) A)) :=
    (IntermediateField.fixingSubgroup_isOpen K).preimage continuous_subtype_val
  obtain ⟨σ, hσ, hne⟩ := ht.exists_tval_ne_zero hU
  have hσ' : (σ : G E Ω) ∈ K.fixingSubgroup := hσ
  have hb : ∀ i, (σ : G E Ω) (algebraMap E' Ω (bQ i)) = algebraMap E' Ω (bQ i) := fun i =>
    (IntermediateField.mem_fixingSubgroup_iff K _).mp hσ' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have : CharZero Ω := (RingHom.charZero_iff (algebraMap E Ω).injective).mp inferInstance
  have hfix : ∀ y : E', (σ : G E Ω) (algebraMap E' Ω y) = algebraMap E' Ω y := by
    intro y
    rw [← bQ.sum_repr y, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_rat_smul, map_rat_smul, hb]
  let τ : G E' Ω := { (σ : G E Ω).toRingEquiv with commutes' := hfix }
  have hτ : resG E τ = (σ : G E Ω) := AlgEquiv.ext fun _ => rfl
  have hτI : τ ∈ Ine (F := E') A := mem_Ine_of_resG (by rw [hτ]; exact σ.2)
  refine ⟨⟨τ, hτI⟩, ?_⟩
  have e : resIne E A ⟨τ, hτI⟩ = σ := Subtype.ext hτ
  rw [e]
  exact hne

variable {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')
  {l : ℕ} [Fact l.Prime] {n : Type} [Fintype n] [DecidableEq n]

include h h' in

theorem notMem_of_place (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal := by
  intro H
  apply hl
  rw [← h]
  have := (h' _).mpr H
  simpa using this

theorem exists_conj_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (hl' : ((l : ℕ) : 𝓞 E') ∉ w'.asIdeal)
    {t : Ine (F := E) A →* Multiplicative ℤ_[l]} {t' : Ine (F := E') A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') {r : G E Ω →* GL n (Qbar l)} {N : Matrix n n (Qbar l)}
    (hN : IsMonodromy t r N) {φ : Weil h} (hφ : deg φ = 1) {φ' : Weil h'} (hφ' : deg φ' = 1) {c' : Qbar l}
    (hct : ∀ σ, tval t (resIne E A σ) = c' * tval t' σ) :
    ∃ b : Qbar l, ∀ g, exp (b • N) * wdMat t hφ r N (resW h h' g) =
      wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g * exp (b • N) := by
  have hpow : ∀ g : Weil h', ((normV w : ℕ) : Qbar l) ^ deg (resW h h' g) = ((normV w' : ℕ) : Qbar l) ^ deg g :=
    fun g => by rw [deg_resW, zpow_mul, zpow_natCast, ← Nat.cast_pow, ← normV_eq_pow_resF h h']
  have hq0 : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot
  have hq1 : 1 - ((normV w' : ℕ) : Qbar l)⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    exact Nat.cast_ne_one.mpr (one_lt_normV w').ne'
  let D : Weil h' → Qbar l := fun g => c' * tval t' (inePart hφ' g) - tval t (inePart hφ (resW h h' g))
  have hD : ∀ g g', D (g * g') = (((normV w' : ℕ) : Qbar l) ^ deg g')⁻¹ * D g + D g' := fun g g' => by
    simp only [D, map_mul, ht'.tval_inePart_mul hl' hφ', ht.tval_inePart_mul hl hφ, hpow]
    ring
  have hD0 : ∀ g, deg g = 0 → D g = 0 := fun g hg => by
    have e : g = ineIncl h' ⟨g, deg_eq_zero_iff.mp hg⟩ := rfl
    have e2 : ∀ σ : Ine (F := E') A, resW h h' (ineIncl h' σ) = ineIncl h (resIne E A σ) := fun σ => Subtype.ext rfl
    rw [e]
    simp only [D, e2, inePart_ineIncl, hct, sub_self]
  obtain ⟨b, hb⟩ : ∃ b : Qbar l, b = D φ' / (1 - ((normV w' : ℕ) : Qbar l)⁻¹) := ⟨_, rfl⟩
  have key : ∀ g, D g = (1 - (((normV w' : ℕ) : Qbar l) ^ deg g)⁻¹) * b := fun g => by
    have h1 := hD (φ' * g) ((φ' * g)⁻¹ * (g * φ'))
    have h0 : deg ((φ' * g)⁻¹ * (g * φ')) = 0 := by simp only [deg_mul, deg_inv]; ring
    rw [mul_inv_cancel_left, hD0 _ h0, h0, hD, hD, hφ', zpow_one, zpow_zero, inv_one, one_mul,
      add_zero] at h1
    rw [hb, ← mul_div_assoc, eq_div_iff hq1]
    linear_combination -h1
  refine ⟨b, fun g => ?_⟩
  have h2 := hN.mul_exp hl ht (resW h h' g) ((((normV w : ℕ) : Qbar l) ^ deg (resW h h' g))⁻¹ * b)
  rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hq0)] at h2
  have hw : wdMat t' hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g =
      (r (resW h h' g) : Matrix n n (Qbar l)) * exp ((-(c' * tval t' (inePart hφ' g))) • N) := by
    rw [wdMat, smul_smul, show -tval t' (inePart hφ' g) * c' = -(c' * tval t' (inePart hφ' g)) by ring]
    rfl
  rw [hw, wdMat, ← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have k := key g
  simp only [D] at k
  rw [hpow]
  linear_combination k

theorem isWDOf_res (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL n (Qbar l)) {x : WD h}
    (hx : IsWDOf ι r x) : IsWDOf ι (r.comp (resG E (E' := E') (Ω := Ω))) (WD.res h h' x) := by
  obtain ⟨t, ht, φ, hφ, N, a0, hN, ha, rfl⟩ := hx
  have hl' := notMem_of_place h h' hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul E' Ω A w' h' l hl' (t.comp (resIne E A)) (tameL h' hl')
    (ht.1.comp continuous_resIne) ht'.1 ht'.2
  have hct : ∀ σ, tval t (resIne E A σ) = algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) * tval (tameL h' hl') σ := fun σ => by
    have e : (t (resIne E A σ)).toAdd = c * ((tameL h' hl') σ).toAdd := hc σ
    simp only [tval, e, PadicInt.coe_mul, map_mul]
  generalize algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]) = c' at hct
  have hc0 : c' ≠ 0 := by
    intro h0
    obtain ⟨σ, hσ⟩ := exists_tval_resIne_ne (E' := E') ht
    exact hσ (by rw [hct, h0, zero_mul])
  have hN' : IsMonodromy (tameL h' hl') (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) := by
    obtain ⟨U, hU, H⟩ := hN.2
    refine ⟨hN.1.smul c', U.comap (resIne E A), hU.preimage continuous_resIne, fun σ hσ => ?_⟩
    rw [smul_smul, mul_comm (tval _ σ), ← hct]
    exact H _ hσ
  have hφ' : deg (frob h') = 1 := deg_frob
  obtain ⟨bb, hbb⟩ := exists_conj_res h h' hl hl' ht ht' hN hφ hφ' hct
  obtain ⟨b', hb'⟩ := hN'.exists_isFrobSS hl' ht' hφ' ι
  refine ⟨tameL h' hl', ht', frob h', hφ', c' • N, b', hN', hb', ?_⟩
  rw [WD.res_mk]
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul bb)).map (toEndC ι)
  have ha2 : IsFrobSS (fun g => toEndC ι (wdMat t hφ r N (resW h h' g))) (toEndC ι N) (resRep h h' a0) :=
    ⟨ha.1, fun g => ha.2 (resW h h' g)⟩
  have hcomm : ∀ g, (hN'.rep hl' ht' hφ' ι) g * toEndC ι N =
      ((normV w' : ℕ) : ℂ) ^ deg g • (toEndC ι N * (hN'.rep hl' ht' hφ' ι) g) := fun g => by
    have H := hN'.rep_comm hl' ht' hφ' ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at H
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) H
  obtain ⟨b1, hb1⟩ := exists_isFrobSS (hN'.rep hl' ht' hφ' ι) (toEndC ι N) (hN'.isSmooth_rep hl' ht' hφ' ι)
    (hN.1.map (toEndC ι)) hcomm
  have i1 : (resRep h h' a0).Iso b1 := ha2.iso hb1 (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι (wdMat t hφ r N (resW h h' g))) v =
        (toEndC ι (wdMat (tameL h' hl') hφ' (r.comp (resG E (E' := E') (Ω := Ω))) (c' • N) g) *
          (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, hbb, map_mul])
    (fun v => by
      show ((u : End ℂ (n → ℂ)) * toEndC ι N) v = (toEndC ι N * (u : End ℂ (n → ℂ))) v
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : b1.Iso b' := IsFrobSS.iso_of_smul ((map_ne_zero ι).mpr hc0) hb1 (by rw [← toEndC_smul]; exact hb')
  exact WD.sound (i1.trans i2).symm

end

end WeilDeligneRestriction

theorem weil_deligne_restriction_away : K5 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ A w h w' h' hl x hx
  exact WeilDeligneRestriction.isWDOf_res h h' hl ι r hx

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.Pst

namespace PositivityTheory.Pf1.CLGD.K.FontaineRestriction

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]

theorem wdRes_eq {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') :
    PositivityTheory.Pf1.CLGD.DescRes.WD.res h h' = PositivityTheory.Pf1.CLGD.WdRestrict.WD.res h h' := rfl

theorem exists_resBridge {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
    [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Induces Bw) :
    ∃ (LL : FinExt l) (Bw' : LocBridge l E' Ω (Dec (F := E') A) ↥(OL LL)),
      Induces Bw' ∧ PositivityTheory.Pf1.CLGD.WdRestrict.IsResBridge Bw Bw' := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : IsAlgClosure ℚ Ω := Formalism.BasicNotions.Examples₂.LB.isAlgClosureQ E' Ω
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have hA : ∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1 := hj
  haveI := Formalism.BasicNotions.Examples₂.LB.KwF_fin (E := E') Bw.j
  refine ⟨Formalism.BasicNotions.Examples₂.LB.nclo (Formalism.BasicNotions.Examples₂.LB.KwF (E := E') Bw.j),
    Formalism.BasicNotions.Examples₂.LB.bridgeOf (E := E') hA _ (Formalism.BasicNotions.Examples₂.LB.mem_nclo _), hA, fun g => ?_⟩
  refine congrArg (fun τ => τ) (GlobalTheory.PlaceBridge.algEquiv_ext (GlobalTheory.PlaceBridge.denseRange_embedding Bw.j)
    fun x => ?_)
  exact (Formalism.BasicNotions.Examples₂.LB.eDec_comm hA g x).trans
    (Bw.e_comm (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A g) x).symm

end PositivityTheory.Pf1.CLGD.K.FontaineRestriction

namespace PositivityTheory.Pf1.CLGD.K

theorem fontaine_weil_deligne_restriction : K6 := by
  intro E Ω _ _ _ _ _ X l a _ ι r _ P AI _ A w h w' h' O _ _ _ Bw hj hp
  obtain ⟨LL, Bw', hj', hc⟩ := FontaineRestriction.exists_resBridge (E' := X.M) Bw hj
  have e1 : (r.comp (Dec (F := E) A).subtype).comp (PositivityTheory.Pf1.CLGD.WdRestrict.resDec E A) =
      (r.comp (PositivityTheory.Pf1.CLGD.DescRes.resG E (E' := X.M))).comp (Dec (F := X.M) A).subtype :=
    MonoidHom.ext fun _ => rfl
  obtain ⟨h1, h2⟩ := PositivityTheory.Pf1.CLGD.WdRestrict.wdAt_res P ι Bw Bw' h h' hj hj' hc _ hp
  rw [e1] at h1 h2
  exact ⟨↥(OL LL), inferInstance, inferInstance, inferInstance, Bw', hj', h1,
    h2.trans (congrFun (FontaineRestriction.wdRes_eq h h').symm _)⟩

end PositivityTheory.Pf1.CLGD.K
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace SemisimpleInertia

theorem eq_one_of_semisimple {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) (hs : T.IsSemisimple) {m : ℕ} (hd : T.charpoly ∣ (X - 1 : ℂ[X]) ^ m) : T = 1 := by
  have hX : (X - 1 : ℂ[X]) = X - C 1 := by simp
  have h1 : minpoly ℂ T ∣ (X - C (1 : ℂ)) ^ m := by
    rw [← hX]; exact (LinearMap.minpoly_dvd_charpoly T).trans hd
  have hp : Prime (X - C (1 : ℂ)) := prime_X_sub_C 1
  obtain ⟨i, -, hass⟩ := (_root_.dvd_prime_pow hp m).1 h1
  have hsq : Squarefree (minpoly ℂ T) := hs.minpoly_squarefree
  have hi1 : i ≤ 1 := by
    by_contra hlt
    push Not at hlt
    have h2 : (X - C (1 : ℂ)) * (X - C 1) ∣ minpoly ℂ T := by
      rw [← sq]
      exact (pow_dvd_pow _ hlt).trans hass.symm.dvd
    exact hp.not_isUnit (hsq _ h2)
  have h3 : minpoly ℂ T ∣ X - C (1 : ℂ) :=
    hass.dvd.trans (by simpa using pow_dvd_pow (X - C (1 : ℂ)) hi1)
  have h4 : aeval T (X - C (1 : ℂ)) = 0 := by
    obtain ⟨q, hq⟩ := h3
    rw [hq, map_mul, minpoly.aeval, zero_mul]
  simpa [sub_eq_zero] using h4

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem charPol_lpTw_of_deg (x : WD h) (s : ℝ) {t : Weil h} (ht : deg t = 0) :
    (x.lpTw s).charPol t = x.charPol t := by
  obtain ⟨n, b, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ, ht, zpow_zero, one_smul]

end SemisimpleInertia

open SemisimpleInertia in

theorem iwahori_fixed_vector_unipotent : K7 := by
  intro E Ω _ _ _ _ _ A w h rc hrc a σ hσ
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.CompanionTheory.GeoLink.geometricLemma
  have hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness := GlobalTheory.bernsteinZelevinskyFiniteness_holds
  have hSeg : GlobalTheory.Published.SegmentRepresentation := GlobalTheory.CompanionTheory.StdSubTop.segmentRepresentation
  have hZ : GlobalTheory.Published.ZelevinskyPolynomialRing :=
    GlobalTheory.zelevinskyPolynomialRing_of_parts hBZ hSeg (PositivityTheory.Groth.grothendieckRingPolynomial_of_seg hSeg)
  obtain ⟨art, ha, ε, -, L⟩ := id hrc
  refine GlobalTheory.LocGL.UnramSupport.fixed_iwahori_ne_bot hG hZ hBZ (w.adicCompletion E) a σ.V σ.ρ σ.smooth σ.irred ?_
  intro s hs y hy
  have hs' : HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep s := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  have hcusp : y.IsCusp := hs'.isCusp hy
  have hdiv : ∀ t : Weil h, deg t = 0 → (rc y).charPol t ∣ (X - 1 : ℂ[X]) ^ a := by
    intro t ht
    have h1 := L.supp _ s hs' t
    have h2 := hσ t ht
    rw [rec_algNorm hrc σ, charPol_lpTw_of_deg _ _ ht] at h2
    rw [← h2, h1]
    exact Multiset.dvd_prod (Multiset.mem_map_of_mem _ hy)
  have hirr := (L.cusp y).1 hcusp
  obtain ⟨n, b, hb, -⟩ := id hirr
  have hN : b.N = 0 := by
    have h0 := GlobalTheory.LocLanglands.TemperedRec.monodromy_zero_of_irreducible_weilDeligne E Ω A w h (rc y) hirr
    rwa [← hb, WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
  have hI : ∀ τ : Ine (F := E) A, b.ρ (ineIncl h τ) = 1 := by
    intro τ
    have h0 := hdiv (ineIncl h τ) (by simp)
    rw [← hb, WD.charPol_mk] at h0
    exact eq_one_of_semisimple _ (b.semisimple _) h0
  have hunr : (rc y).unr := by
    rw [← hb, WD.unr_mk]
    exact ⟨hN, hI⟩
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  exact isUnramChar_of_isCusp_of_isSpherical hG hBZ hZ _ y hcusp ((hrc.isSpherical_iff y).2 hunr)

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CyclicComposition

section Grp

variable {Γ : Type*} [Group Γ]

theorem cyc_of_isCyclic {H : Subgroup Γ} [H.Normal] (hc : IsCyclic (Γ ⧸ H)) :
    ∃ g : Γ, H ⊔ Subgroup.zpowers g = ⊤ := by
  obtain ⟨q, hq⟩ := hc.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨g, eq_top_iff.2 fun x _ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hq (x : Γ ⧸ H))
  have hx : x = x * (g ^ k)⁻¹ * g ^ k := by group
  rw [hx]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers g k))
  rw [← QuotientGroup.eq_one_iff]
  simp [hk]

theorem isCyclic_of_cyc {H : Subgroup Γ} [H.Normal] (g : Γ) (hg : H ⊔ Subgroup.zpowers g = ⊤) :
    IsCyclic (Γ ⧸ H) := by
  refine ⟨⟨(g : Γ ⧸ H), fun q => ?_⟩⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hle : H ⊔ Subgroup.zpowers g ≤ (Subgroup.zpowers (g : Γ ⧸ H)).comap (QuotientGroup.mk' H) := by
    refine sup_le (fun h hh => ?_) ?_
    · rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff h).2 hh]
      exact Subgroup.one_mem _
    · rw [Subgroup.zpowers_le, Subgroup.mem_comap, QuotientGroup.mk'_apply]
      exact Subgroup.mem_zpowers _
  have hx : x ∈ H ⊔ Subgroup.zpowers g := by rw [hg]; exact Subgroup.mem_top x
  exact hle hx

theorem exists_index_prime {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {p : ℕ} (hp : p.Prime)
    (hd : p ∣ Nat.card Q) : ∃ K : Subgroup Q, K.Normal ∧ K.index = p := by
  obtain ⟨q, hq⟩ := IsCyclic.exists_generator (α := Q)
  have ho : orderOf q = Nat.card Q := orderOf_eq_card_of_forall_mem_zpowers hq
  refine ⟨Subgroup.zpowers (q ^ p), ⟨fun n hn g => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hq g)
    have hc : Commute (q ^ i) n := by
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
      exact (((Commute.refl q).zpow_left i).pow_right p).zpow_right j
    rw [hc.eq, mul_inv_cancel_right]
    exact hn
  · have hc := Subgroup.card_mul_index (Subgroup.zpowers (q ^ p))
    have hd' : p ∣ orderOf q := by rw [ho]; exact hd
    rw [Nat.card_zpowers, orderOf_pow_of_dvd hp.ne_zero hd', ho] at hc
    obtain ⟨m, hm⟩ := hd
    rw [hm, Nat.mul_div_cancel_left m hp.pos] at hc
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hm
        exact absurd hm (Nat.card_pos (α := Q)).ne'
      · exact h
    exact Nat.eq_of_mul_eq_mul_left hm0 (hc.trans (mul_comm p m))

end Grp

section Gal

variable {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]

theorem range_resG (L : IntermediateField E Ω) :
    (resG E (E' := L) (Ω := Ω)).range = L.fixingSubgroup := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun y => hσ y y.2), AlgEquiv.ext fun _ => rfl⟩

variable [NumberField E] [IsAlgClosure E Ω]

def ofIF (L : IntermediateField E Ω) [FiniteDimensional E L] (hcm : IsCMField L) : CMExt E Ω :=
  haveI : NumberField L := NumberField.of_module_finite E L
  haveI : IsAlgClosure L Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) L⟩
  { M := L }

def comp (X₁ : CMExt E Ω) (X₂ : CMExt X₁.M Ω) : CMExt E Ω :=
  letI : Algebra E X₂.M := ((algebraMap X₁.M X₂.M).comp (algebraMap E X₁.M)).toAlgebra
  haveI : IsScalarTower E X₂.M Ω := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap E Ω x = algebraMap X₂.M Ω (algebraMap X₁.M X₂.M (algebraMap E X₁.M x))
    rw [← IsScalarTower.algebraMap_apply X₁.M X₂.M Ω, ← IsScalarTower.algebraMap_apply E X₁.M Ω]
  { M := X₂.M }

omit [NumberField E] [IsAlgClosure E Ω] in
theorem resG_comp (X₁ : CMExt E Ω) (X₂ : CMExt X₁.M Ω) (τ : G (comp X₁ X₂).M Ω) :
    resG E (E' := (comp X₁ X₂).M) (Ω := Ω) τ =
      resG E (E' := X₁.M) (Ω := Ω) (resG X₁.M (E' := X₂.M) (Ω := Ω) τ) :=
  AlgEquiv.ext fun _ => rfl

theorem trace_conj {l a : ℕ} [Fact l.Prime] (p x : GL (Fin a) (Qbar l)) :
    ((p * x * p⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      (x : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_mul]

end Gal

section Lift

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem lift_self (hL : GlobalTheory.Published.LocalLanglandsGL) {a : ℕ} (π : CuspSub E a) (hc : π.IsCsd)
    (hr : (CG.mk π).IsRegAlg) : IsLift Ω (CMExt.self E Ω) π π := by
  refine ⟨hc, hr, ?_⟩
  intro l _ ι r wt HT r' wt' HT' h h'
  obtain ⟨p, hp⟩ := GlobalTheory.TraceConjWeil.main E Ω l a r r' h.cont h'.cont h.ss h'.ss (fun w hw A hA σ => by
    obtain ⟨rc, hrc, -⟩ := hL.1 E Ω A w hA
    obtain ⟨σ0, hσ0, -⟩ := LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E a π w
    exact GlobalTheory.WdTrace.trace_eq_of_isWDOf E Ω l ι a r r' w A hA _ (h.away w hw A hA rc hrc σ0 hσ0)
      (h'.away w hw A hA rc hrc σ0 hσ0) σ)
  refine ⟨p, fun g => ?_⟩
  have e : resG E (E' := (CMExt.self E Ω).M) (Ω := Ω) g = g := AlgEquiv.ext fun _ => rfl
  rw [e]
  exact hp g

theorem range_self : (resG E (E' := (CMExt.self E Ω).M) (Ω := Ω)).range = ⊤ :=
  MonoidHom.range_eq_top.2 fun g => ⟨g, AlgEquiv.ext fun _ => rfl⟩

end Lift

theorem tower_ne_top (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hO : OneStep) : ∀ n : ℕ,
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT → ∀ H : Subgroup (G E Ω), GoodSub H → TrCond r H → H ≠ ⊤ →
      H.index ≤ n →
      ∃ (X : CMExt E Ω) (P : CuspSub X.M a), (resG E (E' := X.M) (Ω := Ω)).range = H ∧ IsLift Ω X π P := by
  intro n
  induction n with
  | zero =>
    intro E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT hne hn
    haveI : IsGalois E Ω := {}
    haveI : Finite (G E Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH.isOpen
    exact absurd (Nat.le_zero.1 hn) Subgroup.index_ne_zero_of_finite
  | succ n ih =>
    intro E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT hne hn
    haveI : IsGalois E Ω := {}
    haveI : Finite (G E Ω ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH.isOpen
    haveI := hH.normal
    have h0 : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h1 : H.index ≠ 1 := fun h => hne (Subgroup.index_eq_one.1 h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
    obtain ⟨g0, hg0⟩ := hH.cyc
    haveI : IsCyclic (G E Ω ⧸ H) := isCyclic_of_cyc g0 hg0
    obtain ⟨K, hKn, hKi⟩ := exists_index_prime (Q := G E Ω ⧸ H) hp (by rwa [← Subgroup.index_eq_card])
    set H1 : Subgroup (G E Ω) := K.comap (QuotientGroup.mk' H) with hH1def
    have hH1i : H1.index = p := by
      rw [hH1def, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective H)]
      exact hKi
    have hHH1 : H ≤ H1 := fun x hx => by
      rw [hH1def, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).2 hx]
      exact K.one_mem
    haveI hH1n : H1.Normal := hKn.comap _
    have hH1o : IsOpen (H1 : Set (G E Ω)) := Subgroup.isOpen_mono hHH1 hH.isOpen
    have hH1c : IsClosed (H1 : Set (G E Ω)) := Subgroup.isClosed_of_isOpen H1 hH1o
    have hH1top : H1 ≠ ⊤ := fun h => hp.ne_one (hH1i.symm.trans (Subgroup.index_eq_one.2 h))
    set L : IntermediateField E Ω := IntermediateField.fixedField H1 with hLdef
    have hLfix : L.fixingSubgroup = H1 := InfiniteGalois.fixingSubgroup_fixedField ⟨H1, hH1c⟩
    haveI hLfd : FiniteDimensional E L := (InfiniteGalois.isOpen_iff_finite L).1 (by rw [hLfix]; exact hH1o)
    haveI hLgal : IsGalois E L := (InfiniteGalois.normal_iff_isGalois L).1 (by rw [hLfix]; exact hH1n)
    have hLcm : IsCMField L := hH.cm L (by rw [hLfix]; exact hHH1)
    have hrk : Module.finrank E L = p := by
      haveI : (⟨H1, hH1c⟩ : ClosedSubgroup (G E Ω)).Normal := hH1n
      rw [← IsGalois.card_aut_eq_finrank, ← hH1i, Subgroup.index_eq_card]
      exact (Nat.card_congr (InfiniteGalois.normalAutEquivQuotient ⟨H1, hH1c⟩).toEquiv).symm
    let X1 : CMExt E Ω := ofIF L hLcm
    have hX1r : (resG E (E' := X1.M) (Ω := Ω)).range = H1 := (range_resG L).trans hLfix
    have hTr : ∃ g, g ∉ (resG E (E' := X1.M) (Ω := Ω)).range ∧
        (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0 := by
      rw [hX1r]
      obtain ⟨g, -, hg, ht⟩ := hT H1 ⊤ hHH1 (lt_top_iff_ne_top.2 hH1top)
      exact ⟨g, hg, ht⟩
    have hX1gal : IsGalois E X1.M := hLgal
    have hX1p : (Module.finrank E X1.M).Prime := by
      show (Module.finrank E L).Prime
      rw [hrk]; exact hp
    obtain ⟨P1, hP1⟩ := hO E Ω a ha π hc hr X1 hX1gal hX1p l ι r wt HT hR hTr
    by_cases hEq : H1 ≤ H
    · exact ⟨X1, P1, hX1r.trans (le_antisymm hEq hHH1), hP1⟩
    obtain ⟨r1, wt1, HT1, hR1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι ha hP1.reg hP1.csd
    obtain ⟨p1, hp1⟩ := hP1.res l ι r wt HT r1 wt1 HT1 hR hR1
    set H' : Subgroup (G X1.M Ω) := H.comap (resG E (E' := X1.M) (Ω := Ω)) with hH'def
    have hH'i : H'.index = H.relIndex H1 := by rw [hH'def, Subgroup.index_comap, hX1r]
    have hrel : H.relIndex H1 * p = H.index := hH1i ▸ Subgroup.relIndex_mul_index hHH1
    have hrel1 : H.relIndex H1 ≠ 1 := fun h => hEq (Subgroup.relIndex_eq_one.1 h)
    have hrel0 : H.relIndex H1 ≠ 0 := fun h => h0 (by rw [← hrel, h, zero_mul])
    have hlt : H'.index ≤ n := by
      rw [hH'i]
      have := hp.two_le
      have := Nat.pos_of_ne_zero hrel0
      nlinarith
    have hne' : H' ≠ ⊤ := fun h => hrel1 (by rw [← hH'i, h, Subgroup.index_top])
    have hinj : Function.Injective (resG E (E' := X1.M) (Ω := Ω)) := resG_injective
    have hcont : Continuous (resG E (E' := X1.M) (Ω := Ω)) := continuous_resG
    haveI hH'n : H'.Normal := hH.normal.comap _
    have hH'good : GoodSub H' := by
      refine ⟨hH'n, hH.isOpen.preimage hcont, ?_, ?_⟩
      · apply cyc_of_isCyclic
        refine isCyclic_of_injective (QuotientGroup.map H' H (resG E (E' := X1.M) (Ω := Ω)) le_rfl) ?_
        intro x y hxy
        induction x using QuotientGroup.induction_on with
        | H x =>
        induction y using QuotientGroup.induction_on with
        | H y =>
        have h2 : ((resG E (E' := X1.M) (Ω := Ω) x : G E Ω) : G E Ω ⧸ H) =
            ((resG E (E' := X1.M) (Ω := Ω) y : G E Ω) : G E Ω ⧸ H) := hxy
        rw [QuotientGroup.eq] at h2 ⊢
        rw [hH'def, Subgroup.mem_comap, map_mul, map_inv]
        exact h2
      · intro L' hL'
        have key : H ≤ (L'.restrictScalars E).fixingSubgroup := by
          intro σ hσ
          obtain ⟨τ, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
          have hτ : τ ∈ L'.fixingSubgroup := hL' hσ
          rw [IntermediateField.mem_fixingSubgroup_iff] at hτ ⊢
          intro x hx
          exact hτ x hx
        exact hH.cm _ key
    have hT' : TrCond r1 H' := by
      intro K1 K2 hK1 hK12
      have hmap1 : H ≤ K1.map (resG E (E' := X1.M) (Ω := Ω)) := by
        intro σ hσ
        obtain ⟨τ, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
        exact ⟨τ, hK1 hσ, rfl⟩
      have hmap2 : K1.map (resG E (E' := X1.M) (Ω := Ω)) < K2.map (resG E (E' := X1.M) (Ω := Ω)) := by
        refine lt_of_le_of_ne (Subgroup.map_mono hK12.le) fun h => hK12.ne ?_
        rw [← Subgroup.comap_map_eq_self_of_injective hinj K1, h, Subgroup.comap_map_eq_self_of_injective hinj K2]
      obtain ⟨g, ⟨τ, hτ2, rfl⟩, hg1, ht⟩ := hT _ _ hmap1 hmap2
      refine ⟨τ, hτ2, fun h => hg1 ⟨τ, h, rfl⟩, ?_⟩
      rw [hp1 τ, trace_conj]
      exact ht
    obtain ⟨X2, P2, hX2r, hX2⟩ := ih X1.M Ω a ha P1 hP1.csd hP1.reg l ι r1 wt1 HT1 hR1 H' hH'good hT' hne' hlt
    refine ⟨comp X1 X2, P2, ?_, hX2.csd, hX2.reg, ?_⟩
    · ext σ
      constructor
      · rintro ⟨τ, rfl⟩
        rw [resG_comp]
        have : resG X1.M (E' := X2.M) (Ω := Ω) τ ∈ H' := by rw [← hX2r]; exact ⟨τ, rfl⟩
        exact this
      · intro hσ
        obtain ⟨τ1, rfl⟩ : σ ∈ (resG E (E' := X1.M) (Ω := Ω)).range := by rw [hX1r]; exact hHH1 hσ
        have : τ1 ∈ (resG X1.M (E' := X2.M) (Ω := Ω)).range := by rw [hX2r]; exact hσ
        obtain ⟨τ, rfl⟩ := this
        exact ⟨τ, resG_comp X1 X2 τ⟩
    · intro l' _ ι' r0 wt0 HT0 r' wt' HT' h0' h'
      obtain ⟨s1, ws1, Hs1, hs1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hP1.reg hP1.csd
      obtain ⟨q1, hq1⟩ := hP1.res l' ι' r0 wt0 HT0 s1 ws1 Hs1 h0' hs1
      obtain ⟨q2, hq2⟩ := hX2.res l' ι' s1 ws1 Hs1 r' wt' HT' hs1 h'
      refine ⟨q2 * q1, fun g => ?_⟩
      refine (hq2 g).trans ?_
      rw [hq1, resG_comp]
      simp only [mul_inv_rev, mul_assoc]

end CyclicComposition

open CyclicComposition in
theorem cyclic_composition_lift : LocalHeckeAlgebra := by
  intro hG hL hO E Ω _ _ _ _ _ _ a ha π hc hr l _ ι r wt HT hR H hH hT
  by_cases hne : H = ⊤
  · subst hne
    exact ⟨CMExt.self E Ω, π, range_self, lift_self hL π hc hr⟩
  · exact tower_ne_top hG hO H.index E Ω a ha π hc hr l ι r wt HT hR H hH hT hne le_rfl

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CMCompositionLift

abbrev cmComp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω) : CMExt E Ω :=
  letI : Algebra E Y.M := ((algebraMap X.M Y.M).comp (algebraMap E X.M)).toAlgebra
  { M := Y.M
    tower := IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply E X.M Ω x, IsScalarTower.algebraMap_apply X.M Y.M Ω]
      rfl }

theorem resG_comp {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (X : CMExt E Ω) (Y : CMExt X.M Ω)
    (g : G (cmComp X Y).M Ω) :
    resG E (E' := (cmComp X Y).M) (Ω := Ω) g = resG E (E' := X.M) (Ω := Ω) (resG X.M (E' := Y.M) (Ω := Ω) g) := by
  ext x
  rfl

theorem resW_comp {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (X : CMExt E Ω) (Y : CMExt X.M Ω) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    {w' : HeightOneSpectrum (𝓞 X.M)} {w'' : HeightOneSpectrum (𝓞 (cmComp X Y).M)}
    (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (h'' : IsPlaceOver A w'') :
    resW (E' := (cmComp X Y).M) h h'' = (resW h h').comp (resW (E := X.M) (E' := Y.M) h' h'') :=
  MonoidHom.ext fun _ => Subtype.ext (AlgEquiv.ext fun _ => rfl)

theorem isLift_comp (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) {E Ω : Type} [Field E] [NumberField E] [IsCMField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ} (ha : 1 ≤ a) {X : CMExt E Ω} {Y : CMExt X.M Ω}
    {π : CuspSub E a} {P : CuspSub X.M a} {P₂ : CuspSub Y.M a}
    (h₁ : IsLift Ω X π P) (h₂ : IsLift Ω Y P P₂) : IsLift Ω (cmComp X Y) π P₂ := by
  refine ⟨h₂.csd, h₂.reg, ?_⟩
  intro l _ ι r wt HT r₂ wt₂ HT₂ hr hr₂
  obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha h₁.reg h₁.csd
  obtain ⟨p₁, hp₁⟩ := h₁.res l ι r wt HT r₁ wt₁ HT₁ hr hr₁
  obtain ⟨p₂, hp₂⟩ := h₂.res l ι r₁ wt₁ HT₁ r₂ wt₂ HT₂ hr₁ hr₂
  refine ⟨p₂ * p₁, fun g => ?_⟩
  rw [hp₂ g, hp₁, resG_comp X Y g]
  simp only [mul_inv_rev, mul_assoc]

end CMCompositionLift

open CMCompositionLift in
theorem cm_composition_lift_holds : WeakLiftRestriction := by
  intro hG hFS hFSp hK2c hK3a hT E Ω _ _ _ _ _ _ a ha π hc hreg A w h U hU
  obtain ⟨ι⟩ : Nonempty (Qbar 2 ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex 2
  induction hU with
  | top =>
    obtain ⟨r, wt, HT, hr⟩ := hG.of_isCsd Ω ι ha hreg hc
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a E Ω 2 a ha r hr.cont
    obtain ⟨H, hgood, hHN, hDec, hsp⟩ := hFSp E Ω A w h N hN hNo
    obtain ⟨X, P, hXr, hXl⟩ := hT E Ω a ha π hc hreg 2 ι r wt HT hr H hgood (hTr H hHN)
    obtain ⟨w', h', -, -, hW⟩ := hK2c E Ω A w h X
    refine ⟨X, P, w', h', ?_, hsp X hXr w' h', hXl⟩
    rw [eq_top_iff]
    intro σ _
    rw [hW, hXr]
    obtain ⟨a', b', hσ⟩ := σ.2
    exact hDec hσ.1
  | @step U V _ hVU hn hp hs ih =>
    obtain ⟨X, P, w', h', hXr, hsp, hXl⟩ := ih
    obtain ⟨r₁, wt₁, HT₁, hr₁⟩ := hG.of_isCsd Ω ι ha hXl.reg hXl.csd
    obtain ⟨N, hN, hNo, hTr⟩ := hK3a X.M Ω 2 a ha r₁ hr₁.cont
    have hVn : (V.comap (resW h h')).Normal := ⟨fun n hn0 g => by
      have hn0' : resW h h' n ∈ V := hn0
      have hgU : resW h h' g ∈ U := by rw [← hXr]; exact MonoidHom.mem_range.mpr ⟨g, rfl⟩
      have key := hn.conj_mem (⟨resW h h' n, hVU hn0'⟩ : U) (Subgroup.mem_subgroupOf.mpr hn0')
        (⟨resW h h' g, hgU⟩ : U)
      rw [Subgroup.mem_subgroupOf] at key
      rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
      simpa using key⟩
    have hVi : (V.comap (resW h h')).index.Prime := by
      rw [Subgroup.index_comap, hXr]; exact hp
    have hVs : SmoothSub (V.comap (resW h h')) := by
      obtain ⟨O, hO, hOV⟩ := hs
      refine ⟨O.comap (resG E), continuous_resG.isOpen_preimage (O : Set (G E Ω)) hO, fun σ hσ hσO => ?_⟩
      rw [Subgroup.mem_comap]
      apply hOV
      · rw [deg_resW, hσ, mul_zero]
      · exact hσO
    obtain ⟨H, hgood, hHN, hiff⟩ := hFS X.M Ω A w' h' hsp (V.comap (resW h h')) hVn hVi hVs N hN hNo
    obtain ⟨Y, P₂, hYr, hYl⟩ := hT X.M Ω a ha P hXl.csd hXl.reg 2 ι r₁ wt₁ HT₁ hr₁ H hgood (hTr H hHN)
    obtain ⟨w'', h'', hsp', -, hW⟩ := hK2c X.M Ω A w' h' Y
    have hR : (resW h' h'').range = V.comap (resW h h') := by
      ext σ
      rw [hW, hYr, hiff]
    refine ⟨cmComp X Y, P₂, w'', h'', ?_, hsp' hsp, isLift_comp hG ha hXl hYl⟩
    rw [resW_comp X Y h h' h'', MonoidHom.range_comp, hR, Subgroup.map_comap_eq, hXr, inf_of_le_right hVU]

end PositivityTheory.Pf1.CLGD.K

end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

namespace CharPolyRestriction

theorem natCast_mem_iff {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v) (n : ℕ) :
    ((n : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ A.valuation ((n : ℕ) : Ω) < 1 := by
  rw [← h ((n : ℕ) : 𝓞 K)]
  simp

theorem natCast_not_mem {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : q ≠ p) (hpv : ((p : ℕ) : 𝓞 K) ∈ v.asIdeal) :
    ((q : ℕ) : 𝓞 K) ∉ v.asIdeal := by
  intro hqv
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne.symm)
  obtain ⟨u, t, hut⟩ := hc.map (Int.castRingHom (𝓞 K))
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal := by
    rw [← hut]
    simp only [map_natCast]
    exact v.asIdeal.add_mem (v.asIdeal.mul_mem_left u hpv) (v.asIdeal.mul_mem_left t hqv)
  exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)

section

variable {E E' Ω : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω]
  [Algebra E E'] [Algebra E Ω] [Algebra E' Ω] [IsScalarTower E E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {w' : HeightOneSpectrum (𝓞 E')}
  (h : IsPlaceOver A w) (h' : IsPlaceOver A w')

theorem charPol_res (x : WD h) (t : Weil h') : WD.charPol (WD.res h h' x) t = WD.charPol x (resW h h' t) := by
  obtain ⟨m, b, rfl⟩ := WD.exists_rep x
  rw [WD.res_mk, WD.charPol_mk, WD.charPol_mk, resRep_ρ]

end

end CharPolyRestriction

open CharPolyRestriction in
theorem char_poly_restriction_holds : IwahoriLocalGlobal := by
  intro hG hB hL _k2c hCL k5 k6 k7 E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT H P AI hT w hw A h O _ _ _ Bw hj σ hσ rc hrc U hU hU1
  obtain ⟨T⟩ := hT
  obtain ⟨Y, P', w', h', hrange, -, hLift⟩ := hCL E Ω a ha π hc hr A w h U hU

  obtain ⟨l', hl'ge, hl'p⟩ := Nat.exists_infinite_primes (l + 1)
  have : Fact l'.Prime := ⟨hl'p⟩
  have hne : l' ≠ l := by omega
  obtain ⟨ι'⟩ : Nonempty (Qbar l' ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l'
  have hlw : ((l : ℕ) : 𝓞 E) ∈ w.asIdeal := hw
  have hl'w : ((l' : ℕ) : 𝓞 E) ∉ w.asIdeal := natCast_not_mem w (Fact.out) hl'p hne hlw
  have hl'w' : ((l' : ℕ) : 𝓞 Y.M) ∉ w'.asIdeal := by
    rw [natCast_mem_iff h', ← natCast_mem_iff h]
    exact hl'w

  obtain ⟨r1, wt1, HT1, H1⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hr hc
  obtain ⟨r1', wt1', HT1', H1'⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι' ha hLift.reg hLift.csd
  obtain ⟨p1, hp1⟩ := hLift.res l' ι' r1 wt1 HT1 r1' wt1' HT1' H1 H1'

  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL Y.M a P' w'
  obtain ⟨rc', hrc', -⟩ := hL.1 Y.M Ω A w' h'

  have hx : IsWDOf ι' r1 (rc (algNorm σ)) := H1.away w hl'w A h rc hrc σ hσ
  have hres : IsWDOf ι' (r1.comp (resG E (E' := Y.M))) (WD.res h h' (rc (algNorm σ))) :=
    k5 E Ω Y l' a ι' r1 H1.cont A w h w' h' hl'w _ hx
  have hres' : IsWDOf ι' r1' (WD.res h h' (rc (algNorm σ))) :=
    IsWDOf.of_conj hl'w' p1 (fun g => by rw [MonoidHom.comp_apply, hp1 g, inv_mul_cancel_right]) hres
  have hx' : IsWDOf ι' r1' (rc' (algNorm σ')) := H1'.away w' hl'w' A h' rc' hrc' σ' hσ'
  have heq : rc' (algNorm σ') = WD.res h h' (rc (algNorm σ)) := IsWDOf.unique hl'w' hx' hres'

  have hfix : PRep.fixed σ'.ρ (SmGL.iwahori (w'.adicCompletion Y.M) (Fin a)) ≠ ⊥ := by
    refine k7 Y.M Ω A w' h' rc' hrc' a σ' fun t ht => ?_
    rw [heq, charPol_res]
    refine hU1 _ ?_ ?_
    · rw [← hrange]
      exact ⟨t, rfl⟩
    · rw [deg_resW, ht, mul_zero]

  obtain ⟨r2, wt2, HT2, H2⟩ := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal.of_isCsd hG Ω ι ha hLift.reg hLift.csd
  obtain ⟨p2, hp2⟩ := hLift.res l ι r wt HT r2 wt2 HT2 H H2
  have hpst : IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) := H.isPstAt hB T h Bw hj
  obtain ⟨O', _, _, _, Bw', hj', hpst', h6⟩ := k6 E Ω Y l a ι r H.cont P AI ⟨T⟩ A w h w' h' O Bw hj hpst
  obtain ⟨-, hconj⟩ := GlobalTheory.PstConj.main Y.M Ω l ι a P AI ⟨T⟩ w' A h' O' Bw' hj'
    ((r.comp (resG E (E' := Y.M))).comp (Dec (F := Y.M) A).subtype) (r2.comp (Dec (F := Y.M) A).subtype) p2
    (fun g => hp2 g) hpst'
  have hiw := ((H2.above P AI ⟨T⟩ w' A h' O' Bw' hj').iwahori σ' hσ' hfix).2 rc' hrc'
  refine ⟨Y, w', h', hrange, ?_⟩
  rw [← h6, ← hconj, hiw, heq]

end PositivityTheory.Pf1.CLGD.K

end
end

section
namespace PositivityTheory.Pf1.CLGD.K

theorem main_holds (hW : WBC) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (hL : GlobalTheory.Published.LocalLanglandsGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : Main :=
  char_poly_restriction_holds hG hB hL split_places_weil_galois (cm_composition_lift_holds hG (CyclicCMExtension.cyclic_cm_extension_prescribed_weil weil_element_exists) (cm_descent_avoiding_field weil_element_exists) split_places_weil_galois place_membership_of_sup (cyclic_composition_lift hG hL (oneStep_of hW frobenius_trace_place_norm conjugate_place_norm_under weak_lift_galois_restriction hL hJ))) weil_deligne_restriction_away fontaine_weil_deligne_restriction iwahori_fixed_vector_unipotent

end PositivityTheory.Pf1.CLGD.K
end
