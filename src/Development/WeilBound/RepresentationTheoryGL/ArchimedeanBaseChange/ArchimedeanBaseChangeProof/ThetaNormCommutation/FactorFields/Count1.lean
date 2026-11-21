import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TwistedTraceFormulaEllipticExpansion
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PAbsSum
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.TensorCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTwistedClassesCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTwistContinuousInvolutionIntegralProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralTwistedConjInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyBezoutSeparableDerivativeAdicIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjEtaleMemCentralizerMulIntegralGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalUnitAlmostAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSetCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCharPolyCoeffBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticPolynomialsBoundedFinite
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PClsOnto
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PStruct
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NegOneNotSqSqrtTwo
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PBaseFrame
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PLocDict
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.FactorFields.PParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount

section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinCl2P

theorem rel_of_eqvGen {G : Type} [Group G] (θ : G →* G) {x y : G}
    (h : Relation.EqvGen (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x y) : ∃ g, y = g⁻¹ * x * θ g := by
  induction h with
  | rel a b hab => exact hab
  | refl a => exact ⟨1, by simp⟩
  | symm a b _ ih =>
    obtain ⟨g, rfl⟩ := ih
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  | trans a b c _ _ ih1 ih2 =>
    obtain ⟨g, rfl⟩ := ih1
    obtain ⟨k, rfl⟩ := ih2
    exact ⟨g * k, by rw [map_mul]; group⟩

theorem twConj_of_mk_eq {G : Type} [Group G] {θ : G →* G} {x y : G}
    (h : (Quot.mk _ x : TwCl θ) = Quot.mk _ y) : ∃ g, y = g⁻¹ * x * θ g :=
  rel_of_eqvGen θ (Quot.eqvGen_exact h)

theorem rep_mk {G : Type} [Group G] {θ : G →* G} (y : G) :
    ∃ g, TwCl.rep (Quot.mk _ y : TwCl θ) = g⁻¹ * y * θ g :=
  twConj_of_mk_eq (θ := θ) (Quot.out_eq (Quot.mk _ y : TwCl θ)).symm

theorem charpoly_rep_mk {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (y : GLw n w) : (nrmL n w (TwCl.rep (Quot.mk _ y : TwCl (thL n w)))).val.charpoly = (nrmL n w y).val.charpoly := by
  obtain ⟨g, hg⟩ := rep_mk (θ := thL n w) y
  rw [hg, GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g y, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
    Matrix.charpoly_units_conj']

end PositivityTheory.Rg.BcB.G3.FinCl2P

open PositivityTheory.Rg.BcB.G3.FinCl2P in
theorem PositivityTheory.Rg.BcB.G3.finCl2_pf : FinCl2 := by
  intro E _ _ _ hU a b w Q₁ Q₂ h₁ h₂
  set θ := (thL a w).prodMap (thL b w) with hθ
  let f : TwCl θ → TwCl (thL a w) × TwCl (thL b w) := fun l => (Quot.mk _ l.rep.1, Quot.mk _ l.rep.2)
  have hinj : Function.Injective f := by
    intro l l' hll'
    obtain ⟨g₁, hg₁⟩ := twConj_of_mk_eq (congrArg Prod.fst hll')
    obtain ⟨g₂, hg₂⟩ := twConj_of_mk_eq (congrArg Prod.snd hll')
    have hq : (Quot.mk _ l.rep : TwCl θ) = Quot.mk _ l'.rep :=
      Quot.sound ⟨(g₁, g₂), Prod.ext (by simpa [hθ] using hg₁) (by simpa [hθ] using hg₂)⟩
    have e1 : (Quot.mk _ l.rep : TwCl θ) = l := Quot.out_eq l
    have e2 : (Quot.mk _ l'.rep : TwCl θ) = l' := Quot.out_eq l'
    rw [← e1, ← e2, hq]
  have hA := (GlobalTheory.BCT.ClsFin.classes_finite E hU a w Q₁ h₁).1
  have hB := (GlobalTheory.BCT.ClsFin.classes_finite E hU b w Q₂ h₂).1
  refine ((hA.prod hB).preimage hinj.injOn).subset ?_
  rintro l ⟨hl₁, hl₂⟩
  refine ⟨?_, ?_⟩
  · change (nrmL a w (TwCl.rep (Quot.mk _ l.rep.1 : TwCl (thL a w)))).val.charpoly = Q₁
    rw [charpoly_rep_mk hU a w, hl₁]
  · change (nrmL b w (TwCl.rep (Quot.mk _ l.rep.2 : TwCl (thL b w)))).val.charpoly = Q₂
    rw [charpoly_rep_mk hU b w, hl₂]
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Invar2P

theorem index_ne_zero_of_open_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (K U : Subgroup G) (hK : IsCompact (K : Set G)) (hU : IsOpen (U : Set G)) (R : Subgroup K)
    (hR : U.subgroupOf K ≤ R) : R.index ≠ 0 := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (Subgroup.subgroupOf_isOpen K U hU)
  have h0 : (U.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  intro h
  apply h0
  exact Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hR)

end PositivityTheory.Rg.BcB.G3.Invar2P

namespace PositivityTheory.Rg.BcB.G3

theorem invar2_pf : Invar2 := by
  intro E _ _ _ hU a b w K₁ K₂ hK₁ hK₂ φ hφ y g
  obtain ⟨-, -, -, -, hOa, hCa, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU a w
  obtain ⟨-, -, -, -, hOb, hCb, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU b w
  refine GlobalTheory.TwOrbConj.twOrb_twConj _ _ _ y g φ fun x => ?_
  refine Invar2P.index_ne_zero_of_open_le ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) (K₁.prod K₂)
    (by rw [Subgroup.coe_prod]; exact hCa.prod hCb) (by rw [Subgroup.coe_prod]; exact hK₁.1.prod hK₂.1) _ ?_
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  rw [GlobalTheory.TwOrbConj.mem_rStab]
  intro u
  have hθk : ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) ∈ K₁.prod K₂ :=
    Subgroup.mem_prod.2 ⟨hK₁.2.2 _ (Subgroup.mem_prod.1 hk).1, hK₂.2.2 _ (Subgroup.mem_prod.1 hk).2⟩
  have e : ((x * ((u * k : _) : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * ((u * k : _) : GLw a w × GLw b w))) =
      (k : GLw a w × GLw b w)⁻¹ * ((x * (u : GLw a w × GLw b w))⁻¹ * y * ((thL a w).prodMap (thL b w)) (x * (u : GLw a w × GLw b w))) *
        ((thL a w).prodMap (thL b w)) (k : GLw a w × GLw b w) := by
    simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]; group
  show φ _ = φ _
  rw [e, (hφ.2 _ hθk _).2, (hφ.2 _ ((K₁.prod K₂).inv_mem hk) _).1]

end PositivityTheory.Rg.BcB.G3
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.SuppP
end PositivityTheory.Rg.BcB.G3.SuppP

theorem PositivityTheory.Rg.BcB.G3.supp_pf : PositivityTheory.Rg.BcB.G3.Supp := by
  intro G _ _ θ K y f h
  by_contra hne
  push Not at hne
  apply h
  unfold twOrb avg
  simp only [hne, finsum_zero, mul_zero]
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.GenUnitP

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  rw [hR, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun q hq => absurd (Subsingleton.elim q 1) hq)]
  simp

theorem ind_const {G : Type} [Group G] (θ : G →* G) (K : Subgroup G) (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * y * θ (x * k))) =
      fun _ => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * y * θ x) := by
  funext k
  have e : (x * (k : G))⁻¹ * y * θ (x * k) = (k : G)⁻¹ * (x⁻¹ * y * θ x) * θ k := by
    simp only [map_mul, _root_.mul_inv_rev]; group
  rw [e]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from
      K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) (hKθ _ k.2)), Set.indicator_of_mem (show _ ∈ (K : Set G) from hm)]
    rfl
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), Set.indicator_of_notMem]
    intro h
    apply hm
    have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem (hKθ _ k.2))
    simpa [mul_assoc] using this

theorem summand_eq {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G)
    (hKθ : ∀ k ∈ K, θ k ∈ K) (y x : G) :
    GlobalTheory.TwOrbConj.summand θ K y ((K : Set G).indicator 1) x =
      if x⁻¹ * y * θ x ∈ K then
        (((twCent θ y ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent θ y)) : ℕ) : ℂ) else 0 := by
  unfold GlobalTheory.TwOrbConj.summand
  rw [ind_const θ K hKθ y x, avg_const]
  by_cases hm : x⁻¹ * y * θ x ∈ K
  · rw [Set.indicator_of_mem (show _ ∈ (K : Set G) from hm), if_pos hm]; simp
  · rw [Set.indicator_of_notMem (show _ ∉ (K : Set G) from hm), if_neg hm]; simp

end PositivityTheory.Rg.BcB.G3.GenUnitP

theorem PositivityTheory.Rg.BcB.G3.genUnit_pf : PositivityTheory.Rg.BcB.G3.GenUnit := by
  intro G _ _ _ θ K z hKθ hzK huniq hcptK g
  have hidx : ∀ x : G, (rStab fun k : K =>
      (K : Set G).indicator (1 : G → ℂ) ((x * k)⁻¹ * z * θ (x * k))).index ≠ 0 := by
    intro x
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.ind_const θ K hKθ z x]
    have : rStab (fun _ : K => (K : Set G).indicator (1 : G → ℂ) (x⁻¹ * z * θ x)) = ⊤ := by
      ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
    rw [this, Subgroup.index_top]
    exact one_ne_zero
  rw [GlobalTheory.TwOrbConj.twOrb_twConj G θ K z g ((K : Set G).indicator 1) hidx]
  have hcpt : cptPart (twCent θ z) ≤ twCent θ z ⊓ K :=
    le_inf ((Subgroup.closure_le _).2 fun t ht => ht.1)
      ((Subgroup.closure_le _).2 fun t ht => hcptK t ht.1 ht.2)
  have hval : GlobalTheory.TwOrbConj.summand θ K z ((K : Set G).indicator 1) 1 = 1 := by
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z 1, if_pos (by simpa using hzK),
      GlobalTheory.TwOrbConj.map_conj_self K (K.one_mem), (Subgroup.relIndex_eq_one).2 hcpt]
    simp
  rw [GlobalTheory.TwOrbConj.twOrb_eq, finsum_eq_single _ (DoubleCoset.mk (twCent θ z) K 1)]
  · obtain ⟨t, ht, k, hk, he⟩ := (DoubleCoset.eq _ _ _ _).1
      (DoubleCoset.out_eq' (twCent θ z) K (DoubleCoset.mk (twCent θ z) K 1)).symm
    rw [he, GlobalTheory.TwOrbConj.summand_rep θ K z _ 1 ht hk, hval]
  · intro q hq
    rw [PositivityTheory.Rg.BcB.G3.GenUnitP.summand_eq θ K hKθ z]
    split_ifs with hm
    · exfalso
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := huniq _ hm
      symm
      conv_rhs => rw [← DoubleCoset.out_eq' (twCent θ z) K q]
      rw [DoubleCoset.eq]
      exact ⟨t, ht, k, hk, by rw [he]; group⟩
    · rfl
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.LocGoodP

theorem nrmL_mem {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z : GLw n w) (hz : z ∈ GlobalTheory.LFun.KGL w n) : nrmL n w z ∈ GlobalTheory.LFun.KGL w n := by
  obtain ⟨-, -, hKθ, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  unfold nrmL
  split_ifs with hs
  · exact hz
  · have : thetaGL n (cj w) z = thL n w z := by unfold thL; rw [if_neg hs]
    rw [this]
    exact (GlobalTheory.LFun.KGL w n).mul_mem hz (hKθ _ hz)

theorem commute_nrmL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (z t : GLw n w) (ht : t ∈ twCent (thL n w) z) : t * nrmL n w z = nrmL n w z * t := by
  obtain ⟨-, hinv, -⟩ := GlobalTheory.BCT.ThBasic.twist_basic E hU n w
  have ht' : t * z = z * thL n w t := ht
  by_cases hs : IsSplitAt w
  · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
    have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
    rw [hn1]; rw [hθ1] at ht'; simpa using ht'
  · have hn1 : nrmL n w z = z * thL n w z := by
      unfold nrmL; rw [if_neg hs]; unfold thL; rw [if_neg hs]
    rw [hn1]
    calc t * (z * thL n w z) = z * thL n w t * thL n w z := by rw [← mul_assoc, ht']
      _ = z * thL n w (t * z) := by simp only [map_mul, mul_assoc]
      _ = z * thL n w (z * thL n w t) := by rw [ht']
      _ = z * thL n w z * t := by simp only [map_mul, hinv, mul_assoc]

end PositivityTheory.Rg.BcB.G3.LocGoodP

open PositivityTheory.Rg.BcB.G3.LocGoodP in
theorem PositivityTheory.Rg.BcB.G3.locGood_pf : LocGood := by
  intro E _ _ _ hU n P hP
  filter_upwards [GlobalTheory.BCT.SepBezout.bezout_eventually E P hP.2.2.1,
    GlobalTheory.BCT.UnitStable.eventually_separable (E := E) P hP.2.2.1] with w hgood hsep
  intro z hzK hz
  have hgood₀ : ∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w z).val.charpoly + v * derivative (nrmL n w z).val.charpoly = 1 := by
    rw [hz]; exact hgood
  have hNK := nrmL_mem hU n w z hzK
  refine ⟨fun g hg => ?_, fun t ht hc => ?_, fun y hyK hy => ?_⟩
  · by_cases hs : IsSplitAt w
    · have hθ1 : thL n w = MonoidHom.id _ := by unfold thL; rw [if_pos hs]
      have hn1 : nrmL n w z = z := by unfold nrmL; rw [if_pos hs]
      rw [hn1] at hgood₀
      rw [hθ1] at hg
      obtain ⟨t, ht, k, hk, rfl⟩ := GlobalTheory.SplitUniq.splitUniq E n w z g hzK hgood₀ hg
      refine ⟨t, ?_, k, hk, rfl⟩
      show t * z = z * thL n w t
      rw [hθ1]; exact ht
    · exact GlobalTheory.InertUniq.eq_twCent_mul_KGL E hU n w hs z g hzK hgood₀ hg
  · exact GlobalTheory.StabInt.mem_KGL_of_commute E n w (nrmL n w z) t hNK hgood₀ (commute_nrmL hU n w z t ht) hc
  · exact GlobalTheory.BCT.UnitStable.twConj_of_mem hU n w (atPl w P) hsep z y hz hy hzK hyK
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Unit2P

theorem isCompact_fst {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space G]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.1 : Set G)) := by
  have hc : IsCompact (Prod.fst '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_fst
  have hs : (Subgroup.zpowers t.1 : Set G) ⊆ Prod.fst '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

theorem isCompact_snd {G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [T2Space H]
    (t : G × H) (h : IsCompact (closure (Subgroup.zpowers t : Set (G × H)))) :
    IsCompact (closure (Subgroup.zpowers t.2 : Set H)) := by
  have hc : IsCompact (Prod.snd '' closure (Subgroup.zpowers t : Set (G × H))) := h.image continuous_snd
  have hs : (Subgroup.zpowers t.2 : Set H) ⊆ Prod.snd '' closure (Subgroup.zpowers t : Set (G × H)) := by
    rintro x ⟨k, rfl⟩
    exact ⟨t ^ k, subset_closure ⟨k, rfl⟩, by simp⟩
  exact hc.of_isClosed_subset isClosed_closure (closure_minimal hs hc.isClosed)

end PositivityTheory.Rg.BcB.G3.Unit2P

namespace PositivityTheory.Rg.BcB.G3

theorem unit_pair_of_support (h1 : LocGood) (h2 : GenUnit) (h3 : Supp) : Unit2 := by
  intro E _ _ _ hU a b P₁ hP₁ P₂ hP₂
  filter_upwards [h1 E hU a P₁ hP₁, h1 E hU b P₂ hP₂] with w hw1 hw2
  intro y z hy1 hy2 hz1 hz2 hzK
  obtain ⟨hA1, hB1, hC1⟩ := hw1 z.1 (Subgroup.mem_prod.1 hzK).1 hz1
  obtain ⟨hA2, hB2, hC2⟩ := hw2 z.2 (Subgroup.mem_prod.1 hzK).2 hz2
  set K := (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) with hK
  set θ := (thL a w).prodMap (thL b w) with hθ
  have hnt : ∀ (m : ℕ) (g y : GLw m w),
      (nrmL m w (g⁻¹ * y * thL m w g)).val.charpoly = (nrmL m w y).val.charpoly := by
    intro m g y
    rw [ThBasic.nrmL_twist hU, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hconjK : ∀ y' ∈ K, (nrmL a w y'.1).val.charpoly = atPl w P₁ → (nrmL b w y'.2).val.charpoly = atPl w P₂ →
      ∃ g, y' = g⁻¹ * z * θ g := by
    intro y' hy' e1 e2
    obtain ⟨g1, hg1⟩ := hC1 y'.1 (Subgroup.mem_prod.1 hy').1 e1
    obtain ⟨g2, hg2⟩ := hC2 y'.2 (Subgroup.mem_prod.1 hy').2 e2
    exact ⟨(g1, g2), Prod.ext hg1 hg2⟩
  refine ⟨?_, fun hyK => hconjK y hyK hy1 hy2⟩
  by_cases hex : ∃ g, y = g⁻¹ * z * θ g
  · rw [if_pos hex]
    obtain ⟨g, rfl⟩ := hex
    refine h2 _ θ K z ?_ hzK ?_ ?_ g
    · intro k hk
      exact Subgroup.mem_prod.2 ⟨ThBasic.thL_mem_KGL hU a w _ (Subgroup.mem_prod.1 hk).1,
        ThBasic.thL_mem_KGL hU b w _ (Subgroup.mem_prod.1 hk).2⟩
    · intro g hg
      obtain ⟨t1, ht1, k1, hk1, e1⟩ := hA1 g.1 (Subgroup.mem_prod.1 hg).1
      obtain ⟨t2, ht2, k2, hk2, e2⟩ := hA2 g.2 (Subgroup.mem_prod.1 hg).2
      refine ⟨(t1, t2), ?_, (k1, k2), Subgroup.mem_prod.2 ⟨hk1, hk2⟩, Prod.ext e1 e2⟩
      have ht1' : t1 * z.1 = z.1 * thL a w t1 := ht1
      have ht2' : t2 * z.2 = z.2 * thL b w t2 := ht2
      show (t1, t2) * z = z * θ (t1, t2)
      exact Prod.ext ht1' ht2'
    · intro t ht hc
      have ht' : t * z = z * θ t := ht
      have e1 : t.1 * z.1 = z.1 * thL a w t.1 := congrArg Prod.fst ht'
      have e2 : t.2 * z.2 = z.2 * thL b w t.2 := congrArg Prod.snd ht'
      exact Subgroup.mem_prod.2 ⟨hB1 t.1 e1 (Unit2P.isCompact_fst t hc), hB2 t.2 e2 (Unit2P.isCompact_snd t hc)⟩
  · rw [if_neg hex]
    by_contra hne
    obtain ⟨g, hg⟩ := h3 _ θ K y _ hne
    have hmem : g⁻¹ * y * θ g ∈ K := by
      by_contra hm
      exact hg (Set.indicator_of_notMem (show g⁻¹ * y * θ g ∉ (K : Set (GLw a w × GLw b w)) from hm) _)
    have c1 : (nrmL a w (g⁻¹ * y * θ g).1).val.charpoly = atPl w P₁ := by
      show (nrmL a w (g.1⁻¹ * y.1 * thL a w g.1)).val.charpoly = _
      rw [hnt]; exact hy1
    have c2 : (nrmL b w (g⁻¹ * y * θ g).2).val.charpoly = atPl w P₂ := by
      show (nrmL b w (g.2⁻¹ * y.2 * thL b w g.2)).val.charpoly = _
      rw [hnt]; exact hy2
    obtain ⟨h, hh⟩ := hconjK _ hmem c1 c2
    apply hex
    refine ⟨h * g⁻¹, ?_⟩
    calc y = g * (g⁻¹ * y * θ g) * (θ g)⁻¹ := by group
      _ = g * (h⁻¹ * z * θ h) * (θ g)⁻¹ := by rw [hh]
      _ = (h * g⁻¹)⁻¹ * z * θ (h * g⁻¹) := by rw [map_mul, map_inv]; group

end PositivityTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.Count2P

theorem rel_equiv {G : Type} [Group G] (θ : G →* G) :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by rw [map_inv]; group⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by rw [map_mul]; group⟩

theorem mk_eq_iff {G : Type} [Group G] (θ : G →* G) (x z : G) :
    (Quot.mk (fun x y : G => ∃ g, y = g⁻¹ * x * θ g) x : TwCl θ) = Quot.mk _ z ↔ ∃ g, x = g⁻¹ * z * θ g := by
  constructor
  · intro h
    exact (rel_equiv θ).symm ((rel_equiv θ).eqvGen_iff.1 (Quot.eqvGen_exact h))
  · intro h
    exact (Quot.sound ((rel_equiv θ).symm h))

theorem prod_rel {G H : Type} [Group G] [Group H] (θ₁ : G →* G) (θ₂ : H →* H) (x z : G × H) :
    (∃ g : G × H, x = g⁻¹ * z * (θ₁.prodMap θ₂) g) ↔
      (∃ g₁, x.1 = g₁⁻¹ * z.1 * θ₁ g₁) ∧ (∃ g₂, x.2 = g₂⁻¹ * z.2 * θ₂ g₂) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨g.1, rfl⟩, ⟨g.2, rfl⟩⟩
  · rintro ⟨⟨g₁, h₁⟩, ⟨g₂, h₂⟩⟩
    exact ⟨(g₁, g₂), Prod.ext h₁ h₂⟩

theorem charpoly_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E)
    (x z : GLw n w) (h : ∃ g, x = g⁻¹ * z * thL n w g) :
    (nrmL n w x).val.charpoly = (nrmL n w z).val.charpoly := by
  obtain ⟨g, rfl⟩ := h
  have h1 : nrmL n w (g⁻¹ * z * thL n w g) = g⁻¹ * nrmL n w z * g := GlobalTheory.BCT.ThBasic.nrmL_twist hU n w g z
  have h2 : ((g⁻¹ * nrmL n w z * g : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      ((g⁻¹ : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) * (nrmL n w z : Matrix (Fin n) (Fin n) _) *
        (g : Matrix (Fin n) (Fin n) _) := rfl
  rw [h1, h2, Matrix.coe_units_inv]
  exact Matrix.charpoly_units_conj' g _

end PositivityTheory.Rg.BcB.G3.Count2P

open PositivityTheory.Rg.BcB.G3.Count2P in
theorem PositivityTheory.Rg.BcB.G3.count2_pf (h1 : Count1) : Count2 := by
  intro E _ _ _ hU a b S hS P₁ hP₁ P₂ hP₂ y hy hint
  obtain ⟨zz, hzz, hzK⟩ : ∃ zz : ∀ w : Pl E, GLw a w × GLw b w,
      (∀ w, (Quot.mk _ (zz w) : TwCl ((thL a w).prodMap (thL b w))) = y w) ∧
        ∀ᶠ w in cofinite, zz w ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
    refine ⟨fun w => if h : ∃ z ∈ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)),
        y w = Quot.mk _ z then h.choose else (y w).rep, fun w => ?_, hint.mono fun w hw => ?_⟩
    · dsimp only
      split_ifs with h
      · exact h.choose_spec.2.symm
      · exact Quot.out_eq _
    · dsimp only
      rw [dif_pos hw]
      exact hw.choose_spec.1
  have hrel : ∀ w, ∃ g, (y w).rep = g⁻¹ * zz w * ((thL a w).prodMap (thL b w)) g := by
    intro w
    rw [← mk_eq_iff, hzz w]
    exact Quot.out_eq _
  have hc1 : ∀ w, (nrmL a w (zz w).1).val.charpoly = atPl w P₁ := fun w => by
    rw [← (hy w).1]
    exact (charpoly_eq hU a w _ _ ((prod_rel _ _ _ _).1 (hrel w)).1).symm
  have hc2 : ∀ w, (nrmL b w (zz w).2).val.charpoly = atPl w P₂ := fun w => by
    rw [← (hy w).2]
    exact (charpoly_eq hU b w _ _ ((prod_rel _ _ _ _).1 (hrel w)).2).symm
  have e1 : Nat.card {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
      ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} * 2 ^ nfac P₁ =
      2 ^ (a * Fintype.card (InfinitePlace E)) :=
    h1 E hU a S hS P₁ hP₁ (fun w => (zz w).1) hc1 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).1)
  have e2 : Nat.card {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
      ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} * 2 ^ nfac P₂ =
      2 ^ (b * Fintype.card (InfinitePlace E)) :=
    h1 E hU b S hS P₂ hP₂ (fun w => (zz w).2) hc2 (hzK.mono fun w hw => (Subgroup.mem_prod.1 hw).2)
  have key : ∀ (c : TwCl (thE E a) × TwCl (thE E b)) (w : Pl E),
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w ↔
        (∃ g, locEl a w c.1.rep = g⁻¹ * (zz w).1 * thL a w g) ∧
          (∃ g, locEl b w c.2.rep = g⁻¹ * (zz w).2 * thL b w g) := by
    intro c w
    rw [← hzz w]
    exact (mk_eq_iff _ _ _).trans (prod_rel _ _ _ _)
  let eqv : {c : TwCl (thE E a) × TwCl (thE E b) // ((c.1.rep * thE E a c.1.rep).val.charpoly = P₁ ∧
      (c.2.rep * thE E b c.2.rep).val.charpoly = P₂) ∧ ∀ w ∈ S,
      (Quot.mk _ (locEl a w c.1.rep, locEl b w c.2.rep) : TwCl ((thL a w).prodMap (thL b w))) = y w} ≃
      {c : TwCl (thE E a) // (c.rep * thE E a c.rep).val.charpoly = P₁ ∧
        ∀ w ∈ S, ∃ g, locEl a w c.rep = g⁻¹ * (zz w).1 * thL a w g} ×
      {c : TwCl (thE E b) // (c.rep * thE E b c.rep).val.charpoly = P₂ ∧
        ∀ w ∈ S, ∃ g, locEl b w c.rep = g⁻¹ * (zz w).2 * thL b w g} :=
    { toFun := fun c => (⟨c.1.1, c.2.1.1, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).1⟩,
        ⟨c.1.2, c.2.1.2, fun w hw => ((key c.1 w).1 (c.2.2 w hw)).2⟩)
      invFun := fun p => ⟨(p.1.1, p.2.1), ⟨p.1.2.1, p.2.2.1⟩,
        fun w hw => (key (p.1.1, p.2.1) w).2 ⟨p.1.2.2 w hw, p.2.2.2 w hw⟩⟩
      left_inv := fun c => rfl
      right_inv := fun p => rfl }
  rw [Nat.card_congr eqv, Nat.card_prod, add_mul, pow_add, pow_add, ← e1, ← e2]
  ring

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FinPol2P

theorem isLevel_KGL {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.LFun.KGL w n) :=
  ⟨(GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n).1, le_rfl, fun k hk => GlobalTheory.BCT.ThBasic.thL_mem_KGL hU n w k hk⟩

end PositivityTheory.Rg.BcB.G3.FinPol2P

open PositivityTheory.Rg.BcB.G3.FinPol2P in
theorem PositivityTheory.Rg.BcB.G3.finPol2_pf : FinPol2 := by
  intro E _ _ _ hU a b S hS φ hφc hφ1
  have hC₁ : ∀ w, IsCompact (Prod.fst '' tsupport (φ w)) := fun w => (hφc w).image continuous_fst
  have hC₂ : ∀ w, IsCompact (Prod.snd '' tsupport (φ w)) := fun w => (hφc w).image continuous_snd
  choose γ₁ hγ₁0 hγ₁ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E a w _ (hC₁ w)
  choose γ₂ hγ₂0 hγ₂ using fun w => GlobalTheory.LocBound.bound_charpoly_nrmL E b w _ (hC₂ w)
  let good : Pl E → Prop := fun w => φ w = (((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) : Subgroup _) :
    Set (GLw a w × GLw b w)).indicator 1
  let g₁ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₁ w
  let g₂ : Pl E → WithZero (Multiplicative ℤ) := fun w => if good w then 1 else γ₂ w
  have hfin₁ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E a S hS g₁
    (fun w => by by_cases h : good w <;> simp [g₁, h, hγ₁0]) (hφ1.mono fun w h => by simp [g₁, good, h])
  have hfin₂ := GlobalTheory.BCT.GeoFin.finite_ell_bounded E b S hS g₂
    (fun w => by by_cases h : good w <;> simp [g₂, h, hγ₂0]) (hφ1.mono fun w h => by simp [g₂, good, h])
  refine (hfin₁.prod hfin₂).subset ?_
  rintro p ⟨h₁, h₂, hp⟩
  have key : ∀ w ∈ S, ((∀ i, Valued.v ((atPl w p.1).coeff i) ≤ g₁ w) ∧ (g₁ w)⁻¹ ≤ Valued.v ((atPl w p.1).coeff 0)) ∧
      ((∀ i, Valued.v ((atPl w p.2).coeff i) ≤ g₂ w) ∧ (g₂ w)⁻¹ ≤ Valued.v ((atPl w p.2).coeff 0)) := by
    intro w hw
    obtain ⟨y, hy, e₁, e₂⟩ := hp w hw
    rw [← e₁, ← e₂]
    by_cases hg : good w
    · simp only [g₁, g₂, if_pos hg, inv_one]
      have hy' : y ∈ (GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b) := by
        have hy2 := hy
        rw [show φ w = _ from hg] at hy2
        by_contra hc
        exact hy2 (Set.indicator_of_notMem hc _)
      exact ⟨GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E a w (isLevel_KGL hU a w) y.1 hy'.1,
        GlobalTheory.BCT.GeoFin.charpoly_nrmL_integral E b w (isLevel_KGL hU b w) y.2 hy'.2⟩
    · simp only [g₁, g₂, if_neg hg]
      have hyt : y ∈ tsupport (φ w) := subset_tsupport _ hy
      exact ⟨hγ₁ w y.1 ⟨y, hyt, rfl⟩, hγ₂ w y.2 ⟨y, hyt, rfl⟩⟩
  exact ⟨⟨h₁, fun w hw => (key w hw).1⟩, ⟨h₂, fun w hw => (key w hw).2⟩⟩

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem skewEx_pf : SkewEx := by
  intro E _ _ _
  obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
    by_contra h
    push Not at h
    exact IsCMField.complexConj_ne_one (K := E) (AlgEquiv.ext h)
  have hconj : IsCMField.complexConj E (x - IsCMField.complexConj E x) = -(x - IsCMField.complexConj E x) := by
    rw [map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have hmem : (x - IsCMField.complexConj E x) ^ 2 ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_pow, hconj, neg_sq]
  exact ⟨x - IsCMField.complexConj E x, ⟨_, hmem⟩, sub_ne_zero.mpr (Ne.symm hx), hconj, rfl⟩

end PositivityTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.FactorFieldP

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

abbrev cj (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E : E →+* E)

theorem emb_cj (φ : E →+* ℂ) : φ.comp (cj E) = (starRingEnd ℂ).comp φ := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E φ x

theorem conj_eq_inv {z : ℂ} (h : ‖z‖ = 1) : (starRingEnd ℂ) z = z⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h]
  simp

abbrev Good (Q : E[X]) : Prop := ∀ τ : E →+* ℂ, ∀ z ∈ (Q.map τ).roots, ‖z‖ = 1

variable (Q : E[X]) [Fact (Irreducible Q)]

instance finL : Module.Finite E (AdjoinRoot Q) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finite

instance nfL : NumberField (AdjoinRoot Q) := NumberField.of_module_finite E (AdjoinRoot Q)

theorem root_norm (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) : ‖ψ (AdjoinRoot.root Q)‖ = 1 := by
  apply h (ψ.comp (AdjoinRoot.of Q))
  rw [Polynomial.mem_roots (Polynomial.map_ne_zero (Fact.out : Irreducible Q).ne_zero), Polynomial.IsRoot,
    Polynomial.eval_map, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero]

theorem csr (h : Good Q) :
    Polynomial.eval₂ ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ Q = 0 := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [Polynomial.hom_eval₂, map_zero, map_inv₀, ← conj_eq_inv (root_norm Q h ψ), ← RingHom.comp_assoc, emb_cj,
    ← Polynomial.hom_eval₂, ← Polynomial.hom_eval₂, AdjoinRoot.eval₂_root, map_zero, map_zero]

def sig (h : Good Q) : AdjoinRoot Q →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp (cj E)) (AdjoinRoot.root Q)⁻¹ (csr Q h)

theorem sig_of (h : Good Q) (x : E) : sig Q h (AdjoinRoot.of Q x) = AdjoinRoot.of Q (IsCMField.complexConj E x) := by
  unfold sig
  erw [AdjoinRoot.lift_of]
  rfl

theorem sig_root (h : Good Q) : sig Q h (AdjoinRoot.root Q) = (AdjoinRoot.root Q)⁻¹ := by
  unfold sig
  exact AdjoinRoot.lift_root _

theorem emb_sig (h : Good Q) (ψ : AdjoinRoot Q →+* ℂ) (x : AdjoinRoot Q) :
    ψ (sig Q h x) = starRingEnd ℂ (ψ x) := by
  have e : ψ.comp (sig Q h) = (starRingEnd ℂ).comp ψ := by
    apply AdjoinRoot.ringHom_ext
    · ext y
      simp only [RingHom.coe_comp, Function.comp_apply, sig_of]
      exact IsCMField.complexEmbedding_complexConj E (ψ.comp (AdjoinRoot.of Q)) y
    · simp only [RingHom.coe_comp, Function.comp_apply, sig_root, map_inv₀]
      rw [conj_eq_inv (root_norm Q h ψ)]
  exact RingHom.congr_fun e x

theorem sig_sig (h : Good Q) (x : AdjoinRoot Q) : sig Q h (sig Q h x) = x := by
  let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
  apply ψ.injective
  rw [emb_sig, emb_sig, Complex.conj_conj]

theorem sig_alg (h : Good Q) (x : maximalRealSubfield E) :
    sig Q h (algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x) =
      algebraMap (maximalRealSubfield E) (AdjoinRoot Q) x := by
  show sig Q h (AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)) =
    AdjoinRoot.of Q (algebraMap (maximalRealSubfield E) E x)
  rw [sig_of]
  congr 1
  exact (IsCMField.complexConj E).commutes x

def Kf (h : Good Q) : IntermediateField (maximalRealSubfield E) (AdjoinRoot Q) :=
  (RingHom.eqLocusField (sig Q h) (RingHom.id _)).toIntermediateField fun x => sig_alg Q h x

theorem mem_Kf (h : Good Q) {x : AdjoinRoot Q} : x ∈ Kf Q h ↔ sig Q h x = x := Iff.rfl

theorem totReal (h : Good Q) : IsTotallyReal (Kf Q h) := by
  refine ⟨fun w => ?_⟩
  rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
  letI : Algebra (Kf Q h) ℂ := w.embedding.toAlgebra
  let ψ : AdjoinRoot Q →ₐ[Kf Q h] ℂ := IsAlgClosed.lift
  ext x
  have hx : w.embedding x = ψ.toRingHom (x : AdjoinRoot Q) := (ψ.commutes x).symm
  rw [ComplexEmbedding.conjugate_coe_eq, hx, ← emb_sig Q h ψ.toRingHom, (mem_Kf Q h).1 x.2]

theorem decomp (h : Good Q) {S : AdjoinRoot Q} (hS : S ≠ 0) (hσS : sig Q h S = -S) (z : AdjoinRoot Q) :
    ∃ a b : Kf Q h, z = (a : AdjoinRoot Q) + S * (b : AdjoinRoot Q) := by
  have h2 : (2 : AdjoinRoot Q) ≠ 0 := two_ne_zero
  refine ⟨⟨(z + sig Q h z) / 2, ?_⟩, ⟨(z - sig Q h z) / (2 * S), ?_⟩, ?_⟩
  · rw [mem_Kf, map_div₀, map_add, sig_sig, map_ofNat]
    ring
  · rw [mem_Kf, map_div₀, map_sub, map_mul, sig_sig, map_ofNat, hσS]
    field_simp
    ring
  · show z = (z + sig Q h z) / 2 + S * ((z - sig Q h z) / (2 * S))
    field_simp
    ring

theorem finrank_KL (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (Kf Q h) (AdjoinRoot Q) = 2 := by
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q h (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  have hle : Module.finrank (Kf Q h) (AdjoinRoot Q) ≤ 2 := by
    have hspan : Submodule.span (Kf Q h) (Set.range ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]) = ⊤ := by
      refine eq_top_iff.2 fun z _ => ?_
      obtain ⟨a, b, hz⟩ := decomp Q h hS hσS z
      have e : z = a • (1 : AdjoinRoot Q) + b • AdjoinRoot.of Q s := by
        rw [hz, Algebra.smul_def, Algebra.smul_def, mul_one]
        exact congrArg (fun t => (a : AdjoinRoot Q) + t) (mul_comm _ _)
      rw [e]
      exact Submodule.add_mem _ (Submodule.smul_mem _ a (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ b (Submodule.subset_span ⟨1, rfl⟩))
    have := finrank_range_le_card (R := Kf Q h) ![(1 : AdjoinRoot Q), AdjoinRoot.of Q s]
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
    exact this
  have hne1 : Module.finrank (Kf Q h) (AdjoinRoot Q) ≠ 1 := by
    intro h1
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : AdjoinRoot Q) one_ne_zero).1 h1 (AdjoinRoot.of Q s)
    rw [Algebra.smul_def, mul_one] at hc
    have hm : AdjoinRoot.of Q s ∈ Kf Q h := hc ▸ c.2
    rw [mem_Kf, hσS] at hm
    have h2 : (2 : AdjoinRoot Q) * AdjoinRoot.of Q s = 0 := by linear_combination (-1 : AdjoinRoot Q) * hm
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact two_ne_zero h3
    · exact hS h3
  have hpos : 0 < Module.finrank (Kf Q h) (AdjoinRoot Q) := Module.finrank_pos
  omega

theorem finrank_Kf (h : Good Q) {s : E} (hs : s ≠ 0) (hsc : IsCMField.complexConj E s = -s) :
    Module.finrank (maximalRealSubfield E) (Kf Q h) = Q.natDegree := by
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) E (AdjoinRoot Q)
  haveI : IsScalarTower (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h2 := Module.finrank_mul_finrank (maximalRealSubfield E) (Kf Q h) (AdjoinRoot Q)
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E,
    (AdjoinRoot.powerBasis (Fact.out : Irreducible Q).ne_zero).finrank, AdjoinRoot.powerBasis_dim] at h1
  rw [finrank_KL Q h hs hsc] at h2
  omega

end PositivityTheory.Rg.BcB.G3.FactorFieldP

open PositivityTheory.Rg.BcB.G3.FactorFieldP in
theorem PositivityTheory.Rg.BcB.G3.factorField_pf : FactorField := by
  intro E _ _ _ s d hs hsc hd Q _ hmon hQ
  have hS : AdjoinRoot.of Q s ≠ 0 := (_root_.map_ne_zero _).2 hs
  have hσS : sig Q hQ (AdjoinRoot.of Q s) = -AdjoinRoot.of Q s := by
    rw [sig_of, hsc, map_neg]
  refine ⟨Kf Q hQ, inferInstance, inferInstance, inferInstance, (Kf Q hQ).val.toRingHom, sig Q hQ,
    totReal Q hQ, finrank_Kf Q hQ hs hsc, fun x => rfl, fun x => sig_of Q hQ x, ?_, fun a => a.2, ?_⟩
  · rw [sig_root, inv_mul_cancel₀]
    intro h0
    let ψ : AdjoinRoot Q →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have := root_norm Q hQ ψ
    rw [h0, map_zero, norm_zero] at this
    exact zero_ne_one this
  · intro z
    obtain ⟨a, b, hz⟩ := decomp Q hQ hS hσS z
    exact ⟨a, b, hz⟩
end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.QuadFieldP

open QuadraticAlgebra

theorem not_sq_of_real (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E)
    (d : maximalRealSubfield E) (hs0 : s ≠ 0) (hs : IsCMField.complexConj E s = -s)
    (hd : algebraMap (maximalRealSubfield E) E d = s ^ 2) (K : Type) [Field K]
    [Algebra (maximalRealSubfield E) K] (τ : K →+* ℂ) (t : ℂ) (ht : starRingEnd ℂ t = t) :
    t ^ 2 ≠ τ (algebraMap (maximalRealSubfield E) K d) := by
  intro h
  let _ := (τ.comp (algebraMap (maximalRealSubfield E) K)).toAlgebra
  let φ : E →ₐ[maximalRealSubfield E] ℂ := IsAlgClosed.lift
  have h1 : (φ s) ^ 2 = τ (algebraMap (maximalRealSubfield E) K d) := by
    rw [← map_pow, ← hd, φ.commutes]; rfl
  have hu : starRingEnd ℂ (φ s) = - φ s := by
    have h' := IsCMField.complexEmbedding_complexConj E φ.toRingHom s
    simpa [hs] using h'.symm
  have hu0 : φ s ≠ 0 := by
    intro h0; exact hs0 (φ.toRingHom.injective (by simpa using h0))
  rw [← h1] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h2 | h2
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by rw [← h2]; exact ht
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3
  · apply hu0
    have : starRingEnd ℂ (φ s) = φ s := by
      have := congrArg Neg.neg ht
      rw [h2, map_neg, neg_neg, neg_neg] at this
      exact this
    have h3 : (2 : ℂ) * φ s = 0 := by linear_combination hu - this
    simpa using h3

end PositivityTheory.Rg.BcB.G3.QuadFieldP

namespace PositivityTheory.Rg.BcB.G3

open QuadFieldP QuadraticAlgebra in
theorem quadField_pf : QuadField := by
  intro E _ _ _ s d hs0 hs hd K _ _ _ hKr
  refine ⟨?_, ?_⟩
  · rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← IsCMField.card_infinitePlace_eq_card_infinitePlace E,
      InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyReal.nrComplexPlaces_eq_zero, add_zero,
      ← IsTotallyReal.finrank, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) K, mul_comm]
  generalize hδ : algebraMap (maximalRealSubfield E) K d = δ
  have hkey : ∀ (τ : K →+* ℂ) (t : ℂ), starRingEnd ℂ t = t → t ^ 2 ≠ τ δ := by
    intro τ t ht
    rw [← hδ]
    exact not_sq_of_real E s d hs0 hs hd K τ t ht
  have hns : ∀ r : K, r ^ 2 ≠ δ + 0 * r := by
    intro r hr
    let τ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have hre := ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal τ)
    refine hkey τ (τ r) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [← map_pow, hr, zero_mul, add_zero]
  have : Fact (∀ r : K, r ^ 2 ≠ δ + 0 * r) := ⟨hns⟩
  have hq := GlobalTheory.QuadSymbol.Model.isQuadratic δ
  have hnf := GlobalTheory.QuadSymbol.Model.numberField δ
  have : FiniteDimensional K (QuadraticAlgebra K δ 0) :=
    Module.Finite.of_basis (QuadraticAlgebra.basis δ 0)
  refine ⟨QuadraticAlgebra K δ 0, inferInstance, hnf, inferInstance, hq, ?_, ?_, ?_⟩
  · refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro hre
    let e := w.embedding
    refine hkey (e.comp (algebraMap K _)) (e (ω : QuadraticAlgebra K δ 0)) ?_ ?_
    · rw [← ComplexEmbedding.conjugate_coe_eq, hre]
    · rw [RingHom.comp_apply, ← map_pow, sq, omega_mul_omega_eq_algebraMap]; simp
  · intro x
    rw [GlobalTheory.QuadSymbol.mem_globalNorms_iff]
    have key := GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt (A := K) δ (x := x)
    rw [GlobalTheory.QuadSymbol.mem_normGroup_iff] at key
    simp only [Algebra.algebraMap_self, RingHom.id_apply] at key
    rw [← key]
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨(Algebra.TensorProduct.lid K _).symm z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
    · rintro ⟨z, hz⟩
      refine ⟨Algebra.TensorProduct.lid K _ z, ?_⟩
      rw [Algebra.norm_eq_of_algEquiv, hz]
  · intro u x
    exact GlobalTheory.QuadSymbol.Model.mem_normGroup_sqrt δ

end PositivityTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.TensorComplP

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  (v : HeightOneSpectrum (𝓞 F))

theorem finite_over : {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 F) = v}.Finite := by
  have := v.isMaximal
  have h := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine (h.preimage (f := HeightOneSpectrum.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩

def phi : v.adicCompletion F ⊗[F] K →+*
    (∀ u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}, u.1.adicCompletion K) :=
  RingHom.pi fun u => GlobalTheory.LFun.toCompl u.2

theorem phi_apply (y : v.adicCompletion F ⊗[F] K) (u : {u : HeightOneSpectrum (𝓞 K) // u.under (𝓞 F) = v}) :
    phi v y u = GlobalTheory.LFun.toCompl u.2 y := rfl

def extZ : v.adicCompletion F ⊗[F] K →ₗ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] K :=
  LinearMap.rTensor K (GlobalTheory.AdelicU.singleFin v)

theorem map_extZ_self (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) (extZ v y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem map_extZ_ne {v' : HeightOneSpectrum (𝓞 F)} (h : v' ≠ v) (y : v.adicCompletion F ⊗[F] K) :
    Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v') (AlgHom.id F K) (extZ v y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [extZ, LinearMap.rTensor_tmul, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [GlobalTheory.AdelicU.evalV_singleFin_ne h, TensorProduct.zero_tmul]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]

theorem phi_injective : Function.Injective (phi (K := K) v) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  have h0 : GlobalTheory.LFun.finAdEquiv F K (extZ v y) = 0 := by
    have hc : ∀ w : HeightOneSpectrum (𝓞 K), GlobalTheory.LFun.finAdEquiv F K (extZ v y) w = 0 := by
      intro w
      by_cases hw : w.under (𝓞 F) = v
      · rw [GlobalTheory.LFun.finAdEquiv_apply hw, map_extZ_self]
        exact (phi_apply v y ⟨w, hw⟩).symm.trans (congrFun hy ⟨w, hw⟩)
      · rw [GlobalTheory.LFun.finAdEquiv_apply rfl, map_extZ_ne v hw, map_zero]
    exact Subtype.ext (funext hc)
  have h1 : extZ v y = 0 := (map_eq_zero_iff _ (GlobalTheory.LFun.finAdEquiv F K).injective).1 h0
  rw [← map_extZ_self v y, h1, map_zero]

theorem phi_surjective : Function.Surjective (phi (K := K) v) := by
  intro z
  obtain ⟨y, hy⟩ := (GlobalTheory.LFun.finAdEquiv F K).surjective
    ⟨fun w => if h : w.under (𝓞 F) = v then z ⟨w, h⟩ else 0, by
      filter_upwards [(finite_over (K := K) v).compl_mem_cofinite] with u hu
      rw [dif_neg (by simpa using hu)]
      exact zero_mem _⟩
  refine ⟨Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (AlgHom.id F K) y, funext fun u => ?_⟩
  rw [phi_apply, ← GlobalTheory.LFun.finAdEquiv_apply u.2, hy]
  show (if h : u.1.under (𝓞 F) = v then z ⟨u.1, h⟩ else 0) = z u
  rw [dif_pos u.2]

end PositivityTheory.Rg.BcB.G3.TensorComplP

open PositivityTheory.Rg.BcB.G3.TensorComplP in
theorem PositivityTheory.Rg.BcB.G3.tensorCompl_pf : TensorCompl := by
  intro F K _ _ _ _ _ v
  refine ⟨RingEquiv.ofBijective (phi v) ⟨phi_injective v, phi_surjective v⟩, fun a u => ?_⟩
  show GlobalTheory.LFun.toCompl u.2 (1 ⊗ₜ[F] a) = _
  rw [GlobalTheory.LFun.toCompl_tmul, map_one, one_mul]

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3.InertBaseP

theorem exists_real (E : Type) [Field E] [NumberField E] [IsCMField E] (y : E)
    (hy : IsCMField.complexConj E y = y) :
    ∃ p : maximalRealSubfield E, algebraMap (maximalRealSubfield E) E p = y := by
  have h := (IsCMField.complexConj_eq_self_iff (K := E) (x := y)).1 hy
  exact ⟨⟨y, h⟩, rfl⟩

theorem decomp (E : Type) [Field E] [NumberField E] [IsCMField E] (s : E) (hs : s ≠ 0)
    (hcs : IsCMField.complexConj E s = -s) (x : E) :
    ∃ p q : maximalRealSubfield E, x = algebraMap _ E p + s * algebraMap _ E q := by
  obtain ⟨p, hp⟩ := exists_real E ((x + IsCMField.complexConj E x) / 2) (by
    rw [map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat]; ring)
  obtain ⟨q, hq⟩ := exists_real E ((x - IsCMField.complexConj E x) / (2 * s)) (by
    rw [map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcs]
    field_simp; ring)
  refine ⟨p, q, ?_⟩
  rw [hp, hq]; field_simp; ring

end PositivityTheory.Rg.BcB.G3.InertBaseP

namespace PositivityTheory.Rg.BcB.G3

theorem inertBase_pf (h1 : TensorCompl) : InertBase := by
  intro E _ _ _ hU s d hs hcs hd w hw
  obtain ⟨hcont, -, -, hin, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨hconj, -⟩ := hin hw
  have h : w.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := rfl
  have hc2 := GlobalTheory.LFun.SplitChart.continuous_complMap (E := E) h
  refine ⟨GlobalTheory.LFun.complMap h, fun x => GlobalTheory.LFun.complMap_algebraMap h x, fun x => ?_, fun z => ?_⟩
  · have heq := (HeightOneSpectrum.denseRange_algebraMap (K := maximalRealSubfield E)
        (w.under (𝓞 (maximalRealSubfield E)))).equalizer (hcont.comp hc2) hc2 (funext fun a => by
          simp only [Function.comp_apply, GlobalTheory.LFun.complMap_algebraMap, hconj, AlgEquiv.commutes])
    exact congrFun heq x
  · obtain ⟨t, rfl⟩ := GlobalTheory.LFun.ConjPlace.toCompl_surjective h z
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a x =>
      obtain ⟨p, q, hx⟩ := InertBaseP.decomp E s hs hcs x
      refine ⟨a * algebraMap _ _ p, a * algebraMap _ _ q, ?_⟩
      simp only [GlobalTheory.LFun.toCompl_tmul, hx, map_mul, map_add, GlobalTheory.LFun.complMap_algebraMap]
      ring
    | add t1 t2 e1 e2 =>
      obtain ⟨a1, b1, f1⟩ := e1
      obtain ⟨a2, b2, f2⟩ := e2
      exact ⟨a1 + a2, b1 + b2, by rw [map_add, f1, f2, map_add, map_add]; ring⟩

end PositivityTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

namespace PositivityTheory.Rg.BcB.G3

theorem splitSq_pf (h1 : TensorCompl) : SplitSq := by
  intro E _ _ _ s d hs hcs hd w hw
  have hcm : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  obtain ⟨u, hne, hu⟩ := hw
  have hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) (w.under (𝓞 (maximalRealSubfield E))) :=
    ⟨u, w, hne, congrArg HeightOneSpectrum.asIdeal hu, rfl⟩
  obtain ⟨τ, -⟩ := GlobalTheory.LFun.SplitChart.exists_splitPrime_eq hcm hv rfl
  refine ⟨τ s, ?_⟩
  have key : τ (algebraMap (maximalRealSubfield E) E d) = τ s * τ s := by rw [hd, pow_two, map_mul]
  exact (τ.commutes d).symm.trans key

end PositivityTheory.Rg.BcB.G3

end
end

section
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.G3
open scoped Classical TensorProduct

theorem PositivityTheory.Rg.BcB.G3.count1_pf (h1 : Param) : Count1 := by
  intro E _ _ _ hU n S hS P hP y hy hint
  obtain ⟨ι, _, K, L, _, _, _, _, _, _, x, hcard, hR, hC, hA, hsum, ⟨e⟩⟩ :=
    h1 E hU n S hS P hP y hy hint
  rw [Nat.card_congr e, Nat.card_pi, ← hcard, ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.card_univ,
    ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => GlobalTheory.QuadSymbol.SignCount.card_classes_mul_two (K i) (L i) (hR i) (hC i) (x i) (hA i)

end
end

section
namespace PositivityTheory.Rg.BcB.G3

theorem param : Param :=
  param_pf skewEx_pf (struct_pf factorField_pf) quadField_pf
    (locDict_pf clsNorm_pf clsOnto_pf clsEq_pf baseFrame_pf (inertBase_pf tensorCompl_pf) (splitSq_pf tensorCompl_pf)
      tensorCompl_pf) clsNorm_pf clsOnto_pf clsEq_pf locGood_pf

theorem count1 : Count1 := count1_pf param

theorem g3 : G8.G3 :=
  twisted_trace_formula_elliptic_expansion absSum_pf finCl2_pf invar2_pf (unit_pair_of_support locGood_pf genUnit_pf supp_pf) (count2_pf count1) supp_pf finPol2_pf

end PositivityTheory.Rg.BcB.G3
end
