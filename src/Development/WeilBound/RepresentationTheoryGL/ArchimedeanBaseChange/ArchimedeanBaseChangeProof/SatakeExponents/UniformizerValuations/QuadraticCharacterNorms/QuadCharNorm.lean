import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdeleMemNsUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryHeckeCharacterNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinityTypeUnitaryHeckeCharCMRestrictingToEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceBelowCMField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjQuotNsUnitsEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjIdeleMapMaxRealSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionIdeleConjMemFiniteUnitIdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsOpenSubgroupAdicUnitsNoRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfield
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticHeckeCharCMEqIdeleInfiniteSignFiniteTri
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommGroupDivEqMulDivMulInvDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleCharacterTrivialOnLocalUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticCharacterTrivialUnitIdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryCharOfOpenSubgroupAndHom

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Fok

theorem quadChar_unrAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    (GlobalTheory.GalOfCusp.quadChar E).UnrAt (w.under (𝓞 (maximalRealSubfield E))) := by
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hu : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    by_cases hs : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E)))
    · exact GlobalTheory.LFun.isUnram_of_isSplit h2 hs
    · refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
      obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hs hu rfl
      have := u.isPrime
      exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 hw
  intro x hx
  have hn := GlobalTheory.LFun.mem_normGroup_of_isUnram h2 hu hx
  change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ x)) = 1
  rw [GlobalTheory.LFun.normSign_localIdele, GlobalTheory.QuadSymbol.eta_eq_one_iff.2 hn, map_one]

theorem cm_quadratic_character_unramified : type_of% GlobalTheory.T.quadratic_character_trivial_unit_ideles := by
  intro E _ _ _ hU b hb
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E),
      w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    have := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) (GlobalTheory.GalOfCusp.quadChar E).1
    (GlobalTheory.GalOfCusp.quadChar E).2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hb) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hb v
  obtain ⟨w, rfl⟩ := hs v
  exact quadChar_unrAt E w (hU w) x hxu

end PositivityTheory.Rg.BcB.F.Fok
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.ConsEta in
open PositivityTheory.Rg.BcB.F.Fok

namespace PositivityTheory.Rg.BcB.F.Fok.Mu2
open GlobalTheory.ConsEta
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infSign_ideleMap_finPartI (b : Neutral.B1.Ideles (maximalRealSubfield E)) :
    infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
  rw [infSign, MonoidHom.finset_prod_apply]
  refine Finset.prod_eq_one fun w _ => ?_
  have : Units.map (GlobalTheory.IdeleNormChar.infEval w)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (GlobalTheory.Mem.Chr.finPartI _ b)) = 1 := by
    refine Units.ext ?_
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E 1) w = 1
    rw [map_one]; rfl
  simp only [MonoidHom.comp_apply, this, map_one]

theorem eta_eq_infSign (hU : Unr E) (b : Neutral.B1.Ideles (maximalRealSubfield E))
    (hb : b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E)) :
    (GlobalTheory.GalOfCusp.quadChar E).1 b = infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) := by
  set f := GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b
  have h1 : ∀ v, ((b * f⁻¹ : Neutral.B1.Ideles _) : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 v = 1 := by
    intro v
    have e : f⁻¹ = GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b⁻¹ := (map_inv _ b).symm
    rw [e]
    exact congrArg (fun z : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E) => z.2 v) b.mul_inv
  have h2 := GlobalTheory.T.quadraticHeckeCharCM_eq_ideleInfiniteSign_finiteTrivial E _ h1
  have h3 := cm_quadratic_character_unramified E hU b hb
  have e1 : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 (b * f⁻¹) * (GlobalTheory.GalOfCusp.quadChar E).1 f := by
    rw [← map_mul, inv_mul_cancel_right]
  have e2 : infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b) =
      infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (b * f⁻¹)) *
        infSign E (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E f) := by
    rw [← map_mul, ← map_mul, inv_mul_cancel_right]
  rw [e1, e2, h2, h3, infSign_ideleMap_finPartI, mul_one]

theorem quadratic_character_square : type_of% GlobalTheory.T.exists_unitary_hecke_character_norm := by
  intro E _ _ _ hUnr
  obtain ⟨w0, hw0⟩ := GlobalTheory.T.exists_splitPlaceBelowCMField E
  obtain ⟨V, hVo, hV⟩ := GlobalTheory.T.exists_isOpen_subgroup_adicUnits_no_rootsOfUnity E w0
  have hC : Continuous (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) :=
    @GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_ideleMap E E _ _ _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toAlgebra
  refine ⟨GlobalTheory.Mem.Chr.unitIdl E ⊓ (GlobalTheory.Mem.Chr.unitIdl E).comap (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E) ⊓
    V.comap (conjQuot E w0), infSign E, ?_, continuous_infSign, norm_infSign E, ?_⟩
  · exact (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.inter (GlobalTheory.Mem.UnitOpen.isOpen_unitIdl.preimage hC)).inter
      (hVo.preimage (continuous_conjQuot w0))
  intro k b u hu hx
  obtain ⟨⟨hx1, hx2⟩, hx3⟩ := hx
  have hu1 := nsUnits_le_unitIdl hu
  have hCu := GlobalTheory.T.cmExtensionIdeleConj_mem_finiteUnitIdeles E u hu1
  set C := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj (maximalRealSubfield E) E with hCdef
  set I := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b with hI
  set c : Eˣ →* Eˣ := Units.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.conj (maximalRealSubfield E) E).toRingEquiv.toRingHom.toMonoidHom with hc
  have hCx : C (Neutral.B1.diagUnits E k * I * u) = Neutral.B1.diagUnits E (c k) * I * C u := by
    rw [map_mul, map_mul, hI, GlobalTheory.T.cmExtensionIdeleConj_ideleMap_maxRealSubfield]
    congr 2
    exact GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleConj_principalIdele (maximalRealSubfield E) E k
  set x := Neutral.B1.diagUnits E k * I * u with hxdef
  set t : Eˣ := k / c k with ht
  have hdt : Neutral.B1.diagUnits E t = (x / C x) * (u / C u)⁻¹ := by
    rw [hCx, hxdef, ht, _root_.map_div]
    exact commGroup_div_eq_mul_div_mul_inv_div _ _ _ _ _
  have htu : Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    rw [hdt]; exact mul_mem (div_mem hx1 hx2) (inv_mem (div_mem hu1 hCu))
  have hnorm : ∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1 := by
    intro φ
    have h0 : φ (k : E) ≠ 0 := by simp
    have e : φ ((c k : Eˣ) : E) = starRingEnd ℂ (φ k) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.embedding_conj (maximalRealSubfield E) E φ k
    rw [ht, Units.val_div_eq_div_val, map_div₀, e, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 h0)]
  have htor := GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one E t htu hnorm
  have hcqu := GlobalTheory.T.conjQuot_eq_one_of_mem_nsUnits_of_isSplitAt E w0 hw0 u hu
  have hmem : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t ∈ V := by
    have e1 : Units.map (algebraMap E (w0.adicCompletion E)).toMonoidHom t =
        Units.map (GlobalTheory.IdeleNormChar.finEval w0) (Neutral.B1.diagUnits E t) := Units.ext rfl
    have e2 : conjQuot E w0 x = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (x / C x) := rfl
    have e3 : conjQuot E w0 u = Units.map (GlobalTheory.IdeleNormChar.finEval w0) (u / C u) := rfl
    rw [e1, hdt, map_mul, map_inv, ← e2, ← e3, hcqu, inv_one, mul_one]
    exact hx3
  have ht1 := hV t htor hmem
  have hck : c k = k := (div_eq_one.1 ht1).symm
  have hkF : (k : E) ∈ maximalRealSubfield E := by
    refine (IsCMField.complexConj_eq_self_iff E _).1 ?_
    exact congrArg Units.val hck
  set k' : (maximalRealSubfield E)ˣ := Units.mk0 ⟨(k : E), hkF⟩ (fun h => k.ne_zero (congrArg Subtype.val h)) with hk'
  have hdk : Neutral.B1.diagUnits E k =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E (Neutral.B1.diagUnits (maximalRealSubfield E) k') := by
    refine (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap_principalIdele (maximalRealSubfield E) E k').trans ?_ |>.symm
    exact congrArg (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.principalIdele E) (Units.ext rfl)
  set b' := Neutral.B1.diagUnits (maximalRealSubfield E) k' * b with hb'
  have hxb : x = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' * u := by
    rw [hxdef, hdk, hb', map_mul]
  have hηb : (GlobalTheory.GalOfCusp.quadChar E).1 b = (GlobalTheory.GalOfCusp.quadChar E).1 b' := by
    rw [hb', map_mul, (GlobalTheory.GalOfCusp.quadChar E).2.2 k', one_mul]
  have hb'E : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' ∈ GlobalTheory.Mem.Chr.unitIdl E := by
    have : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b' = x * u⁻¹ := by rw [hxb, mul_inv_cancel_right]
    rw [this]; exact mul_mem hx1 (inv_mem hu1)
  rw [hηb, eta_eq_infSign hUnr b' (GlobalTheory.T.mem_finiteUnitIdeles_of_map_maxRealSubfield E b' hb'E), hxb, (infSign E).map_mul _ u, infSign_nsUnits hu, mul_one]

end PositivityTheory.Rg.BcB.F.Fok.Mu2
end

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1

theorem valuation_eq_uniformizer {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : Valued.v x = WithZero.exp (-1 : ℤ)) :
    ValuativeRel.valuation (w.adicCompletion E) x = ValuativeRel.uniformizer (w.adicCompletion E) := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v
  apply le_antisymm
  · rw [ValuativeRel.le_uniformizer_iff, he.lt_one_iff_lt_one, hx, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (ValuativeRel.uniformizer (w.adicCompletion E))
    rw [← hy]
    have h1 : Valued.v y < 1 := by
      rw [← he.lt_one_iff_lt_one, hy]; exact ValuativeRel.uniformizer_lt_one
    rw [he.le_iff_le, hx]
    by_cases hy0 : Valued.v y = 0
    · rw [hy0]; exact zero_le'
    · rw [← WithZero.exp_log hy0] at h1 ⊢
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
      rw [WithZero.exp_le_exp]; omega

theorem valued_eq_one {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {x : w.adicCompletion E} (hx : ValuativeRel.valuation (w.adicCompletion E) x = 1) : Valued.v x = 1 := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E)) Valued.v).eq_one_iff_eq_one.1 hx

theorem loc_same {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (Neutral.B1.localIdele K v x).val.2 v = x := by
  classical
  exact Pi.mulSingle_eq_same v _

theorem loc_ne {K : Type} [Field K] [NumberField K] {v w : HeightOneSpectrum (𝓞 K)} (h : w ≠ v)
    (x : (v.adicCompletion K)ˣ) : (Neutral.B1.localIdele K v x).val.2 w = 1 := by
  classical
  exact Pi.mulSingle_eq_of_ne h _

theorem ideleMap_apply (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : Neutral.B1.Ideles K) (w : HeightOneSpectrum (𝓞 L)) :
    (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap K L a).val.2 w = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap K L w (a.val.2 (w.under (𝓞 K))) := rfl

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteCompletionMap ideleMap)

theorem inert_character_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ μ : HChar E,
    (∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x) →
    (∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w → Valued.v (u : w.adicCompletion E) = 1 →
      μ.1 (Neutral.B1.localIdele E w u) = 1) →
    ∀ w : Pl E, ¬ IsSplitAt w → μ.loc w = GlobalTheory.SmGL.unrChar (w.adicCompletion E) (-1) := by
  intro E _ _ _ hU μ hres hunit w hw
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hns : ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    intro hs
    obtain ⟨a, b, hab, ha, hb⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    apply hw
    rcases eq_or_ne a w with rfl | haw
    · exact ⟨b, hab.symm, hb⟩
    · exact ⟨a, haw, ha⟩
  have hun : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) (w.under (𝓞 (maximalRealSubfield E))) := by
    refine GlobalTheory.LFun.isUnram_iff.2 fun u hu => ?_
    obtain rfl := GlobalTheory.LFun.eq_of_not_isSplit hns hu rfl
    have := u.isPrime
    exact Algebra.isUnramifiedAt_iff_of_isDedekindDomain.1 (hU u)
  have he : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1 := GlobalTheory.LFun.isUnram_iff.1 hun w rfl
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.exists_isUniformiser (w.under (𝓞 (maximalRealSubfield E)))
  set ϖE : (w.adicCompletion E)ˣ := Units.map (finiteCompletionMap (maximalRealSubfield E) E w).toMonoidHom ϖ with hϖE
  have hvE : Valued.v (ϖE : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (finiteCompletionMap (maximalRealSubfield E) E w ϖ) = _
    rw [← GlobalTheory.CharTransport.locMap_eq, ← GlobalTheory.LFun.complMap_rfl, GlobalTheory.LFun.valued_complMap rfl ϖ.ne_zero, he, pow_one]
    exact hϖ
  have hid : ideleMap (maximalRealSubfield E) E (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) =
      Neutral.B1.localIdele E w ϖE := by
    refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun u => ?_))
    · exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap (maximalRealSubfield E) E)
    · rw [ideleMap_apply]
      by_cases hu : u = w
      · subst hu
        rw [loc_same, loc_same]
        rfl
      · have hu' : u.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun e => hu (GlobalTheory.LFun.eq_of_not_isSplit hns e rfl)
        rw [loc_ne hu', loc_ne hu, map_one]
  have hq : (GlobalTheory.GalOfCusp.quadChar E).1 (Neutral.B1.localIdele _ (w.under (𝓞 (maximalRealSubfield E))) ϖ) = -1 := by
    change Units.map _ (GlobalTheory.IdeleNormChar.normSign E (Neutral.B1.localIdele _ _ ϖ)) = -1
    rw [GlobalTheory.LFun.normSign_localIdele]
    have hne := fun h => GlobalTheory.LFun.not_mem_normGroup_of_inert h2 hns hun hϖ (GlobalTheory.QuadSymbol.eta_eq_one_iff.1 h)
    rcases Int.units_eq_one_or (GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E _ ϖ) with h | h
    · exact absurd h hne
    · rw [h]; ext; simp
  have hval : μ.loc w ϖE = -1 := by
    change μ.1 (Neutral.B1.localIdele E w ϖE) = -1
    rw [← hid, hres, hq]
  have hunr : GlobalTheory.SplitWeil.IsUnram (μ.loc w) := fun x hx => hunit w x hw (valued_eq_one w hx)
  rw [GlobalTheory.SmGL.eq_unrChar hunr (valuation_eq_uniformizer w hvE), hval]

end PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Fok.Mu3
open GlobalTheory.MuExist

theorem quadChar_norm (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)) :
    ‖(((GlobalTheory.GalOfCusp.quadChar E).1 b : ℂˣ) : ℂ)‖ = 1 := by
  change ‖((Units.map (Int.castRingHom ℂ).toMonoidHom (GlobalTheory.IdeleNormChar.normSign E b) : ℂˣ) : ℂ)‖ = 1
  rcases Int.units_eq_one_or (GlobalTheory.IdeleNormChar.normSign E b) with h | h <;> rw [h] <;> simp

theorem muExists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e := by
  intro E _ _ _ hU
  obtain ⟨U, ψ, hUo, hψc, hψu, hc⟩ := PositivityTheory.Rg.BcB.F.Fok.Mu2.quadratic_character_square E hU
  let α : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × nsUnits E) →* Neutral.B1.Ideles E :=
    (Neutral.B1.diagUnits E).coprod ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E).coprod (nsUnits E).subtype)
  let a : Eˣ × (Neutral.B1.Ideles (maximalRealSubfield E) × nsUnits E) →* ℂˣ :=
    (GlobalTheory.GalOfCusp.quadChar E).1.comp ((MonoidHom.fst _ _).comp (MonoidHom.snd _ _))
  have hα : ∀ y, α y = Neutral.B1.diagUnits E y.1 * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E y.2.1 *
      (y.2.2 : Neutral.B1.Ideles E) := fun y => by
    simp only [α, MonoidHom.coprod_apply, Subgroup.coe_subtype, mul_assoc]
  obtain ⟨χ, hχc, hχu, -, hχα⟩ := GlobalTheory.exists_unitary_char_of_open_subgroup_and_hom (Neutral.B1.Ideles E) _ U hUo α a ψ
    hψc hψu (fun y => quadChar_norm E y.2.1) (fun y hy => by
      rw [hα] at hy ⊢
      exact hc y.1 y.2.1 y.2.2 y.2.2.2 hy)
  have hk : ∀ k : Eˣ, χ (Neutral.B1.diagUnits E k) = 1 := fun k => by
    have h := hχα (k, 1, 1)
    rw [hα] at h
    simpa [a] using h
  let μ : HChar E := ⟨χ, hχc, hk⟩
  have hres : ∀ x, μ.1 (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E x) = (GlobalTheory.GalOfCusp.quadChar E).1 x :=
    fun x => by
      have h := hχα (1, x, 1)
      rw [hα] at h
      simpa [a] using h
  have hns : ∀ (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ), ¬ IsSplitAt w →
      Valued.v (u : w.adicCompletion E) = 1 → μ.1 (Neutral.B1.localIdele E w u) = 1 := fun w u hw hu => by
    have h := hχα (1, 1, ⟨_, localIdele_mem_nsUnits w u hw hu⟩)
    rw [hα] at h
    simpa [a] using h
  have hunit : μ.IsUnitary := hχu
  obtain ⟨e, he, hz⟩ := GlobalTheory.T.infinityType_unitaryHeckeCharCM_restricting_to_eta E μ hunit hres
  exact ⟨μ, e, hunit, hres, PositivityTheory.Rg.BcB.F.Fok.Mu3Aux1.inert_character_unramified E hU μ hres hns, he, hz⟩

end PositivityTheory.Rg.BcB.F.Fok.Mu3
end
end
