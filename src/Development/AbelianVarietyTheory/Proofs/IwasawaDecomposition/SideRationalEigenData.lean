import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Formalism.LocalToGlobal.NumberFieldFamilies.IsLocalizedOfSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptySpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompactOpenMembership
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientLinearLiftDoubleCosetOperators
import Formalism.LocalToGlobal.NumberFieldFamilies.JMtInjective
import Formalism.LocalToGlobal.Columns.ColumnsProofs.HFSSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKsOfFinExt
import Development.AutomorphicArithmetic.CyclotomicBounds.FiniteDimensionalRoots
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SameTwistOfOneField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStandardFactsOnLocalisationBase
import Formalism.LocalToGlobal.NumberFieldFamilies.HeckeStd0Of
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceDoubleCosetOperatorSemisimpleTypeSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeOperatorsOnLocalisationSpaceSemisimple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRingActsFaithfullyOnLocalisedLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeEigenspaceNeBotEveryLocalisationPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBaseChangeFreeOverLocalisationCoeffRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPadicAlgClRingEquivComplexCompEqOfCountabl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalisationGaloisCharacterContinuous

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.GenHypOut

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (hQ : QOver C)
    (w : D.what₂.places.Pl) (j : Fin D.R.m) (v : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E)
    (hv : GenAt D (D.what₂.places.resChar w) (C.Q w) v k) (hc : IsConjPl D.host v s.w) :
    s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) j) := by
  have hov : NG.OverPl v s.v := GlobalTheory.LocLevel.overPl_of_isConjPl hc
  obtain ⟨_, hl, hS, hvQ, _, _⟩ := hv
  have hp : v ∉ placesOver D.host.E
      (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  rintro (⟨w', hov', kk, hk⟩ | hq)
  · apply hS
    refine ⟨?_, hl⟩
    have hvk := GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hk
    fin_cases kk
    · exact Or.inl hvk
    · exact Or.inr (Or.inl hvk)
  · by_cases htw : D.what₂.muAt w ≠ D.what₂.mu0
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp w htw j hq
      rcases hw' with hQ' | hp'
      · exact hvQ (hQ w w' v hQ' ⟨s.v, hov', hov⟩)
      · exact hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' hp')
    · rw [not_not] at htw
      obtain ⟨hg, w', hov', hu⟩ := hq
      apply hu
      unfold TupTied.tup
      rw [tp.xi_tw, tp.psi_un w htw]
      refine HChar.UnrAt.mul ((cf.isMu0 j).unr w' fun kk hk => hg ⟨w', hov', kk, hk⟩)
        (HChar.UnrAt.mul ?_ (((isPsi_one (D.what₂.places.resChar w)).ram w').2 (Finset.notMem_empty _)))
      have hnp : w' ∉ placesOver D.host.E
          (if D.what₂.places.resChar w = D.host.pde then D.host.pde' else D.host.pde) :=
        fun h => hp (GlobalTheory.LocLevel.mem_placesOver_of_overPl' hov hov' h)
      unfold CharFrame.delAt
      split_ifs with h
      · exact cf.isDel'.unr w' fun h' => hnp (by rw [if_pos h]; exact h')
      · exact cf.isDel.unr w' fun h' => hnp (by rw [if_neg h]; exact h')

theorem genHyp : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C),
    MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  intro D cf M C tp hM hQ w j h1 h2
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  refine ⟨gPl D ∪ qPl D (tp.tup (D.what₂.muTw w) ⟨j', by omega⟩), hM.hyp w ⟨j', by omega⟩, ?_⟩
  intro v k s hv hc
  exact not_mem_bad D cf C tp hQ w _ v k s hv hc

end GlobalTheory.GenHypOut
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable : ∀ (D : D7) (cf : CharFrame D) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), MtInput D M tp.tup C.Q → QOver C → GenHyp M C.Q := by
  atlas_forward_decl GlobalTheory.GenHypOut.genHyp
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.SplitExConj

theorem exists_splitPlace_conj_unif : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) :=
  fun D => GlobalTheory.SplitConjPlace.splitEx_all D

end GlobalTheory.SplitExConj
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer : ∀ (D : D7), (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) := by
  atlas_forward_decl GlobalTheory.SplitExConj.exists_splitPlace_conj_unif
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocCommute

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem hLC_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  classical
  intro D M C hR hstd hgen hsplit j w v k v' k'
  by_cases h : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k
  swap
  · have : hLC (mt0 M) C.Q hR j w v k = 0 := by unfold hLC; rw [dif_neg h]
    rw [this]; exact Commute.zero_left _
  by_cases h' : (1 ≤ j ∧ j ≤ D.R.m) ∧ GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v' k'
  swap
  · have : hLC (mt0 M) C.Q hR j w v' k' = 0 := by unfold hLC; rw [dif_neg h']
    rw [this]; exact Commute.zero_right _
  obtain ⟨⟨h1, h2⟩, hg⟩ := h
  obtain ⟨-, hg'⟩ := h'
  obtain ⟨B, hB, hBv⟩ := hgen w j h1 h2
  obtain ⟨s, ϖ, hc, hu⟩ := hsplit v hg.1
  obtain ⟨s', ϖ', hc', hu'⟩ := hsplit v' hg'.1
  have hsB : s.v ∉ B := hBv v k s hg hc
  have hsB' : s'.v ∉ B := hBv v' k' s' hg' hc'
  have hstd' := hstd D.host.E D.R.nV (M (D.what₂.muTw w) j h1 h2).wt (M (D.what₂.muTw w) j h1 h2).J
    (M (D.what₂.muTw w) j h1 h2).χ B (M (D.what₂.muTw w) j h1 h2).J_open hB s ϖ k hsB hu hg.2.2.2.2.1 hg.2.2.2.2.2
  have hcomm := hstd'.2.2.1 s' ϖ' k' hsB' hu' hg'.2.2.2.2.1 hg'.2.2.2.2.2
  rw [commute_iff_eq]
  ext x
  apply Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective
  apply (M (D.what₂.muTw w) j h1 h2).real_inj
  have hf : (M (D.what₂.muTw w) j h1 h2).real (D.what₂.jMt (D.what₂.muTw w) j x) ∈
      NG.TypeSp (M (D.what₂.muTw w) j h1 h2).wt.ρ (M (D.what₂.muTw w) j h1 h2).J (M (D.what₂.muTw w) j h1 h2).χ := by
    rw [← (M (D.what₂.muTw w) j h1 h2).real_range]; exact LinearMap.mem_range_self _ _
  have e1 := hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hc hu
  have e2 := hLC_spec (mt0 M) C.Q hR j w v' k' h1 h2 hg' s' ϖ' hc' hu'
  simp only [Module.End.mul_apply]
  change (mt0 M (D.what₂.muTw w) j h1 h2).real _ = (mt0 M (D.what₂.muTw w) j h1 h2).real _
  rw [e1, e2, e2, e1]
  exact hcomm _ hf

end GlobalTheory.HeckeLocCommute
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftedHeckeOperators_at_generators_commute : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q), HeckeStdPlain → GenHyp M C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) := by
  atlas_forward_decl GlobalTheory.HeckeLocCommute.hLC_commute
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeSplitField

open Module

theorem aeval_baseChange {L K M : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    (f : Module.End L M) (p : L[X]) :
    aeval (f.baseChange K) (p.map (algebraMap L K)) = (aeval f p).baseChange K := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => rw [Polynomial.map_add, map_add, hp, hr, map_add, LinearMap.baseChange_add]
  | monomial k c =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← LinearMap.baseChange_pow]
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext x
    simp [Module.algebraMap_end_apply, LinearMap.baseChange_tmul]

theorem iSup_maxGen_baseChange {L K M I : Type} [Field L] [Field K] [Algebra L K] [AddCommGroup M] [Module L M]
    [FiniteDimensional L M] (op : I → Module.End L M) (hc : ∀ x y, Commute (op x) (op y)) {p : L[X]}
    (hp : Formalism.L2.Col.HeckePolyFor op p) (hsp : (p.map (algebraMap L K)).Splits) (x : I) :
    ⨆ μ, Module.End.maxGenEigenspace ((op x).baseChange K) μ = ⊤ := by
  classical
  obtain ⟨hp0, s, hs, hd⟩ := hp
  obtain ⟨c, hcx⟩ := hs x
  have e : (op x).baseChange K = ∑ y ∈ s, algebraMap L K (c y) • (op y).baseChange K := by
    rw [hcx]
    change LinearMap.baseChangeHom L K M M (∑ y ∈ s, c y • op y) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    change (c y • op y).baseChange K = _
    rw [LinearMap.baseChange_smul, algebraMap_smul]
  rw [e]
  refine Formalism.L2.Col.hfs_iSup_maxGen_sum s (fun y => (op y).baseChange K) (fun y => algebraMap L K (c y))
    (fun y _ z _ => ?_) (fun y hy => ?_)
  · change _ * _ = _ * _
    rw [← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul, (hc y z).eq]
  · apply Formalism.L2.Col.hfs_iSup_maxGen_of_splits
    refine hsp.of_dvd (Polynomial.map_ne_zero hp0) (minpoly.dvd K _ ?_)
    rw [aeval_baseChange, hd y hy, LinearMap.baseChange_zero]

theorem finiteDimensional_mtL {R : Ranks} (what₂ : Rows.Data R) (μ : what₂.Tup) (j : ℕ) :
    FiniteDimensional what₂.LL (what₂.MtL μ j) := by
  let b := Module.Free.chooseBasis what₂.LL (what₂.MtL μ j)
  haveI : Finite (Module.Free.ChooseBasisIndex what₂.LL (what₂.MtL μ j)) := ((what₂.jMt_basis μ j b).1).finite
  exact Module.Finite.of_basis b

end GlobalTheory.HeckeSplitField

namespace GlobalTheory.HeckeSplitField

open Module

theorem exists_finExt_split : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂),
    (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) →
    ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 →
      F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k →
        ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  intro D M C hR E0 hcomm j w
  classical
  haveI : FiniteDimensional D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) := finiteDimensional_mtL D.what₂ _ j
  let op : HeightOneSpectrum (𝓞 D.host.E) × ℕ → Module.End D.what₂.LL (D.what₂.MtL (D.what₂.muTw w) j) :=
    fun vk => hLC (mt0 M) C.Q hR j w vk.1 vk.2
  obtain ⟨p, hp⟩ := Formalism.L2.Col.hfs_exists_poly op
  let S : Set (PadicAlgCl (D.what₂.places.resChar w)) := ((p.map (E0.emb w)).roots.toFinset : Set _)
  haveI : Finite S := Finset.finite_toSet _
  have hfin : FiniteDimensional ℚ_[D.what₂.places.resChar w] (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] S, hfin⟩, ?_⟩
  intro X hXE hF v k _
  have hmap : (p.map (ecC X j w)).map (iqC X j w) = p.map (E0.emb w) := by
    rw [Polynomial.map_map]
    congr 1
    ext x
    rw [RingHom.comp_apply, iqC_ec, hXE]
  have hsp : (p.map (algebraMap D.what₂.LL (FractionRing (OcC X j w)))).Splits := by
    refine Polynomial.Splits.of_splits_map (iqC X j w) ?_ fun a ha => ?_
    · change ((p.map (ecC X j w)).map (iqC X j w)).Splits
      rw [hmap]
      exact IsAlgClosed.splits _
    · change a ∈ ((p.map (ecC X j w)).map (iqC X j w)).roots at ha
      rw [hmap] at ha
      have haS : a ∈ S := by
        simp only [S, Finset.coe_sort_coe, Finset.mem_coe, Multiset.mem_toFinset]
        exact ha
      exact iqC_surj X j w a (hF (IntermediateField.subset_adjoin _ _ haS))
  exact iSup_maxGen_baseChange op (fun x y => hcomm j w x.1 x.2 y.1 y.2) hp hsp (v, k)

end GlobalTheory.HeckeSplitField
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (E0 : PlEmb D.what₂), (∀ j w v k v' k', Commute (hLC (mt0 M) C.Q hR j w v k) (hLC (mt0 M) C.Q hR j w v' k')) → ∀ (j : ℕ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ X : CoefIn D.what₂, X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∀ v k, GenAt0 D.host (D.what₂.places.resChar w) (C.Q w) v k → ⨆ μ, (hKC (mt0 M) C.Q hR X j w v k).maxGenEigenspace μ = ⊤ := by
  atlas_forward_decl GlobalTheory.HeckeSplitField.exists_finExt_split
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section
namespace GlobalTheory.HeckeLocN

theorem exists_finExt_big (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl) :
    ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧
      ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  classical
  let c := (plEmb pl).emb w
  let S : Finset (Loc.Om (D.what₂.places.resChar w)) := (big w).image (fun z => (pl.ι w).symm z)
  have h1 := GlobalTheory.PlaceBridge.finiteDimensional_adjoin_range c
  have h2 : FiniteDimensional ℚ_[D.what₂.places.resChar w]
      (IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w)))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine ⟨⟨IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c) ⊔
      IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))),
      IntermediateField.finiteDimensional_sup _ _⟩, fun x => ?_, fun z hz => ?_⟩
  · exact (le_sup_left (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ ⟨x, rfl⟩)
  · exact (le_sup_right (a := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (Set.range c)) (b := IntermediateField.adjoin ℚ_[D.what₂.places.resChar w] (S : Set (Loc.Om (D.what₂.places.resChar w))))) (IntermediateField.subset_adjoin _ _ (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hz)))

end GlobalTheory.HeckeLocN
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers : ∀ (D : D7) (pl : PlSide D) (big : D.what₂.places.Pl → Finset ℂ) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), (∀ x, (plEmb pl).emb w x ∈ F0.1) ∧ ∀ z ∈ big w, (pl.ι w).symm z ∈ F0.1 := by
  atlas_forward_decl GlobalTheory.HeckeLocN.exists_finExt_big
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.BridgeAll

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_finExt_ge {l : ℕ} [Fact l.Prime] {ι : Type} (S : Set ι) (hS : S.Finite) (L : ι → Loc.FinExt l) :
    ∃ F : Loc.FinExt l, ∀ i ∈ S, (L i).1 ≤ F.1 := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨⟨⊥, inferInstance⟩, fun i hi => absurd hi (Set.notMem_empty i)⟩
  | @insert a s _ _ ih =>
    obtain ⟨F, hF⟩ := ih
    have h1 := F.2
    have h2 := (L a).2
    refine ⟨⟨(L a).1 ⊔ F.1, IntermediateField.finiteDimensional_sup _ _⟩, ?_⟩
    rintro i (rfl | hi)
    · exact le_sup_left
    · exact (hF i hi).trans le_sup_right

theorem placesOver_finite (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l.Prime) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {(l : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.2 hv

theorem exists_bridge_good {R : Ranks} (H : Host R) (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra H.E Ω]
    [IsAlgClosure H.E Ω] (u : HeightOneSpectrum (𝓞 H.E)) (A : ValuationSubring Ω) (hA : IsPlaceOver A u) :
    ∃ L0 : Loc.FinExt l, u ∈ placesOver H.E l → ∀ LL : Loc.FinExt l, L0.1 ≤ LL.1 →
      ∃ Bw : LocBridge l H.E Ω (Dec (F := H.E) A) ↥(Loc.OL LL),
        (∀ x, x ∈ A ↔ ‖Bw.j x‖ ≤ 1) ∧ Loc.GoodCoef H.condN Bw.LL ∧
        ∀ x : ↥(Loc.OL LL), ((Bw.toLL x : ↥Bw.LL.1) : Loc.Om l) = ((x : ↥LL.1) : Loc.Om l) := by
  by_cases hu : u ∈ placesOver H.E l
  · obtain ⟨j, L0, hj, hB⟩ := GlobalTheory.PlaceBridge.exists_locBridge l H.E Ω u A hu hA
    let L1 : Loc.FinExt l := UpperTheory.KStar.Cyc.rootsExt l _ (UpperTheory.KStar.Cyc.lcm_ne_zero (l := l) H.toHostRaw)
    have f0 := L0.2
    have f1 := L1.2
    refine ⟨⟨L0.1 ⊔ L1.1, IntermediateField.finiteDimensional_sup _ _⟩, fun _ LL hLL => ?_⟩
    obtain ⟨Bw, e1, e2, e3, e4⟩ := hB LL (le_sup_left.trans hLL)
    refine ⟨Bw, by rw [e1]; exact hj, ?_, e4⟩
    rw [e2]
    exact UpperTheory.KStar.Cyc.mem_of_rootsExt_le _ (le_sup_right.trans hLL)
  · exact ⟨⟨⊥, inferInstance⟩, fun h => absurd h hu⟩

theorem brAt_of_large : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w),
    ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  intro D w
  choose L hL using fun u : PlE D.host =>
    exists_bridge_good D.host (D.what₂.places.resChar w) D.nd.Om u (D.nd.plOm.1 u) (D.nd.plOm.2 u)
  obtain ⟨F, hF⟩ := exists_finExt_ge _ (placesOver_finite D.host.E (D.what₂.places.resChar_prime w)) L
  refine ⟨F, fun X j hX u hu => ?_⟩
  obtain ⟨Bw, h1, h2, h3⟩ := hL u hu (X.Kx j w) ((hF u hu).trans hX)
  exact ⟨Bw, h1, h2, fun z => (iqC_alg X j w z).trans (h3 z).symm⟩

end GlobalTheory.HeckeLocN.BridgeAll
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff : ∀ (D : D7) (w : D.what₂.places.Pl), ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), F0.1 ≤ (X.Kx j w).1 → BrAt X j w := by
  atlas_forward_decl GlobalTheory.HeckeLocN.BridgeAll.brAt_of_large
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem GlobalTheory.HeckeLocN.exists_twRing_of_large : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  intro D C F low E0 hT hC w
  obtain ⟨φ, hR, hn, ⟨K, hKf, hK⟩, halg⟩ :=
    GlobalTheory.HeightCounting.SameTw.exists_reads D C F hT w (D.what₂.places.resChar w) (C.twI_l w) (E0.emb w) (E0.emb_w w)
  refine ⟨⟨K, hKf⟩, ?_⟩
  intro X j hXE hle
  let g : D.ntw.O0 (C.twI w) →+* ↥(X.Kx j w).1 := φ.codRestrict (X.Kx j w).1 (fun y => hle (hK y))
  let f : D.ntw.O0 (C.twI w) →+* OcC X j w :=
    g.codRestrict (Loc.OL (X.Kx j w)) (fun y => (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) (g y)).2 (hn y))
  have hf : ∀ y, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) = φ y := fun y => by
    rw [iqC_alg]; rfl
  have e1 : (iqC X j w).comp (ecC X j w) = E0.emb w := by
    ext x; rw [RingHom.comp_apply, iqC_ec, hXE]
  have e2 : (iqC X j w).comp ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) = φ := by
    ext y; exact hf y
  have hRd : GlobalTheory.HeightCounting.SameTw.Reads D C w (ecC X j w) ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) :=
    GlobalTheory.HeightCounting.SameTw.Reads.of_comp (iqC X j w) (by rw [e1, e2]; exact hR)
  refine ⟨f, ?_, hRd, fun hw x y hy => GlobalTheory.HeightCounting.SameTw.Reads.emb hC hw hRd x y hy⟩
  intro z z' hz
  apply Subtype.val_injective
  apply Subtype.val_injective
  change φ _ = _
  rw [halg z z' hz]
  rfl
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  atlas_forward_decl GlobalTheory.HeckeLocN.exists_twRing_of_large
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.FinDimVProof

theorem finDimV_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  intro R H what₂ B j w
  classical
  have hfin : (Formalism.L2.Fam.NPC.LatticeFinitenessFree.latJ (what₂ := what₂) j w).Finite :=
    Set.Finite.subset ((what₂.MtLat (what₂.muTw w) j).gen.finite_toSet.preimage
      ((Formalism.L2.Fam.NPC.LatticeFinitenessFree.jMt_injective (what₂.muTw w) j).injOn)) fun x hx => hx
  have hs := Formalism.L2.Fam.NPC.LatticeFinitenessFree.span_iV (B := B) j w
  exact Module.finite_def.2 ⟨(hfin.image (B.iV j w)).toFinset, by simpa using hs⟩

end GlobalTheory.FinDimVProof
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_localisation_space_all : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂), FinDimV B := by
  atlas_forward_decl GlobalTheory.FinDimVProof.finDimV_all
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem psiInt_of_embW : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  intro D C X ψ0 h j w g
  have hint : ∀ g, ∃ y : OcC X j w, algebraMap (OcC X j w) (FractionRing (OcC X j w)) y =
      ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    intro g
    have h0 : 0 ≤ D.what₂.places.val w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
      (C.embW_w w _).2 ⟨_, (h w g).symm⟩
    exact (ecC_w X j w _).1 h0
  obtain ⟨a, ha⟩ := hint g
  obtain ⟨b, hb⟩ := hint g⁻¹
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))
    rw [map_mul, ha, hb, ← map_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, map_one, map_one]
  exact ⟨Units.mkOfMulEqOne a b hab, ha⟩

end GlobalTheory.HeckeLocN
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacterValues_integral_units_at_place : ∀ (D : D7) (C : NChoice D) (X : CoefIn D.what₂) (ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)), (∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) = algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w) ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w)))) → PsiInt X ψ0 := by
  atlas_forward_decl GlobalTheory.HeckeLocN.psiInt_of_embW
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.CondConj

theorem unrAt_of_under_eq {E : Type} [Field E] [NumberField E] [StarRing E] {F : Type} [Field F] [NumberField F] [Algebra F E]
    (hF : ∀ x : F, star (algebraMap F E x) = algebraMap F E x) (hr : Module.finrank F E = 2)
    (hc : ∃ a : E, star a ≠ a) {χ : HChar E} (hχ : χ.TrivOn F) (ht : ∀ P, χ.TameAt P) {P Q : HeightOneSpectrum (𝓞 E)}
    (hPQ : Q.under (𝓞 F) = P.under (𝓞 F)) (hu : χ.UnrAt P) : χ.UnrAt Q := by
  by_cases e : Q = P
  · rwa [e]
  obtain rfl := ((GlobalTheory.NormOneUnit.under_eq_iff hF hr hc P Q).1 hPQ).resolve_left e
  intro x hx
  obtain ⟨k, y, hk, hy, hcong⟩ := (GlobalTheory.localUnit_congr_global E _ x hx).1
  have hv : (Col.conjPrime₂ P).valuation E (k : E) = 1 := by
    rw [hk]
    exact (HeightOneSpectrum.valuation_eq_one_iff_notMem _).2 hy
  have hkQ : IsUnitAt (Col.conjPrime₂ P) (atFin (Col.conjPrime₂ P) k) :=
    (Formalism.UG.P.levelaf_valued_algebraMap _ (k : E)).trans hv
  have hxk : IsUnitAt (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) := by
    unfold IsUnitAt at hx hkQ ⊢
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hx, hkQ, inv_one, one_mul]
  have h1 : χ.loc (Col.conjPrime₂ P) (x * (atFin (Col.conjPrime₂ P) k)⁻¹) = 1 := ht _ _ hxk (by simpa using hcong)
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  have hs0 : star (k : E) ≠ 0 := star_ne_zero.2 k.ne_zero
  have h2 := GlobalTheory.NormOneProd.split_unit hF hr hc hχ ht (Ne.symm e) (y' := Units.mk0 _ hs0) rfl hv
  rw [GlobalTheory.NormOneUnit.locK_unr hu (y := Units.mk0 _ hs0) ((GlobalTheory.CharVal.valuation_conjP P _).symm.trans hv), one_mul] at h2
  exact h1.trans h2

theorem cond_of_under_eq {R : Ranks} (H : Host R) {l : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 H.E))} {χ : HChar H.E}
    (h : IsPsi l Q χ) {v v' : HeightOneSpectrum (𝓞 H.E)} (hv : v.under (𝓞 H.F) = v'.under (𝓞 H.F)) (hQ : v ∈ Q) : v' ∈ Q := by
  letI := H.cmStar
  haveI : IsCMField H.E := H.isCMField_hostE
  by_contra hn
  refine (h.ram v).1 (unrAt_of_under_eq (F := H.F) (fun x => ?_) ?_ ?_ h.triv h.tame hv ((h.ram v').2 hn)) hQ
  · exact IsCMField.complexConj_apply_eq_self H.E x
  · exact Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield H.E) H.E
  · by_contra hh
    push Not at hh
    exact IsCMField.complexConj_ne_one H.E (AlgEquiv.ext hh)

theorem under_eq_of_conj {R : Ranks} (H : Host R) {v v' : HeightOneSpectrum (𝓞 H.E)} (h : IsConjPl H v v') :
    v.under (𝓞 H.F) = v'.under (𝓞 H.F) := by
  ext a
  refine h (algebraMap (𝓞 H.F) (𝓞 H.E) a) (algebraMap (𝓞 H.F) (𝓞 H.E) a) ?_
  haveI : IsCMField H.E := H.isCMField_hostE
  apply H.φ₀.injective
  rw [Formalism.HC.HostAx.conjE_apply, ← IsCMField.complexEmbedding_complexConj]
  exact congrArg H.φ₀ (IsCMField.complexConj_apply_eq_self H.E (a : H.F)).symm

theorem cond_over_conj : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  intro D cf C tp h0
  have key : ∀ w (v v' : PlE D.host), v.under (𝓞 D.host.F) = v'.under (𝓞 D.host.F) → v ∈ C.Q w → v' ∈ C.Q w := by
    intro w v v' hv hQ
    by_cases hw : TwistedAt D w
    · exact cond_of_under_eq D.host (tp.psi_is w hw) hv hQ
    · rw [h0 w hw] at hQ
      exact absurd hQ (Finset.notMem_empty _)
  refine ⟨fun w v v' hQ ⟨v₀, h1, h2⟩ => key w v v' (HeightOneSpectrum.ext (h1.trans h2.symm)) hQ,
    fun w v v' hQ hc => key w v' v (under_eq_of_conj D.host hc).symm hQ⟩

end GlobalTheory.HeckeLocN.CondConj
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistConductors_over_real_places_and_conj_stable : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C), (∀ w, ¬ TwistedAt D w → C.Q w = ∅) → QOver C ∧ QConj C := by
  atlas_forward_decl GlobalTheory.HeckeLocN.CondConj.cond_over_conj
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
open scoped Pointwise

namespace GlobalTheory.TypePrimeSplit

theorem exists_intCast_of_card {K : Type} [CommRing K] {p : ℕ} (hp : p.Prime) (h : Nat.card K = p) (x : K) :
    ∃ n : ℤ, x = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite K := Nat.finite_of_card_ne_zero (h ▸ hp.ne_zero)
  haveI : Nontrivial K := Finite.one_lt_card_iff_nontrivial.1 (h ▸ hp.one_lt)
  obtain ⟨n, hn⟩ := mem_zmultiples_of_prime_card (G := K) h (g := 1) (g' := x) one_ne_zero
  exact ⟨n, by simpa using hn.symm⟩

theorem isSplitPl_of_card {R : Ranks} (H : Host R) (v : PlE H) {p : ℕ} (hp : p.Prime)
    (h : Nat.card (𝓞 H.E ⧸ v.asIdeal) = p) : IsSplitPl H v := by
  by_contra hn
  have key : ∀ x ∈ v.asIdeal, (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x ∈ v.asIdeal := by
    intro x hx
    by_contra hy'
    refine hn ⟨x, hx, fun z hz => ?_⟩
    have : z = (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x := RingOfIntegers.ext hz
    rwa [this]
  apply H.der.unramEF v.asIdeal v.isPrime v.ne_bot
  intro x
  show (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x ∈ v.asIdeal
  obtain ⟨n, hx⟩ := exists_intCast_of_card hp h (Ideal.Quotient.mk v.asIdeal x)
  have ha : x - n ∈ v.asIdeal := Ideal.Quotient.eq.1 (by rw [hx, map_intCast])
  have h3 := key _ ha
  have hf : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • (n : 𝓞 H.E) = n :=
    map_intCast (MulSemiringAction.toRingHom _ (𝓞 H.E) (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H)) n
  rw [smul_sub, hf] at h3
  have h4 : (PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - x = ((PI.UnitaryGroupMassFormula.HostPrimeFacts.cj H) • x - n) - (x - n) := by ring
  rw [h4]
  exact sub_mem h3 ha

theorem typePrime_split :
    ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v :=
  fun D k v hv => isSplitPl_of_card D.host v (D.host.g_prime k)
    (GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hv)

end GlobalTheory.TypePrimeSplit
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typePrime_places_isSplitPlace : ∀ (D : D7) (k : Fin 2) (v : PlE D.host), v ∈ placesOver D.host.E (D.host.g k) → IsSplitPl D.host v := by
  atlas_forward_decl GlobalTheory.TypePrimeSplit.typePrime_split
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN.TLocal

theorem isLocalRing_of_congr {O X : Type} [CommRing O] [IsLocalRing O] [Finite X] [Nonempty X] (T : Subalgebra O (X → O))
    (h : ∀ f ∈ T, ∀ x y, f x - f y ∈ IsLocalRing.maximalIdeal O) : IsLocalRing T := by
  obtain ⟨x⟩ := ‹Nonempty X›
  have key : ∀ f : T, IsUnit ((f : X → O) x) → IsUnit f := by
    intro f hx
    have : Algebra.IsIntegral T (X → O) := Algebra.IsIntegral.tower_top O
    have hu : IsUnit (algebraMap T (X → O) f) := by
      refine Pi.isUnit_iff.2 fun y => ?_
      by_contra hy
      have h1 := add_mem (h f f.2 x y) ((IsLocalRing.mem_maximalIdeal _).2 hy)
      exact (IsLocalRing.mem_maximalIdeal _).1 (by simpa using h1) hx
    have hl := RingHom.IsIntegral.isLocalHom (f := algebraMap T (X → O))
      (fun g => Algebra.IsIntegral.isIntegral g) Subtype.val_injective
    exact hl.map_nonunit f hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun f => ?_
  exact (IsLocalRing.isUnit_or_isUnit_one_sub_self ((f : X → O) x)).imp (key f) (key (1 - f))

theorem sub_mem_of_ker_eq {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A] (ψ φ : A →ₐ[O] O)
    (h : RingHom.ker ((IsLocalRing.residue O).comp ψ.toRingHom) = RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom))
    (a : A) : ψ a - φ a ∈ IsLocalRing.maximalIdeal O := by
  have h1 : a - algebraMap O A (φ a) ∈ RingHom.ker ((IsLocalRing.residue O).comp φ.toRingHom) := by
    rw [RingHom.mem_ker]; simp
  rw [← h, RingHom.mem_ker] at h1
  rw [← IsLocalRing.residue_eq_zero_iff]
  simpa using h1

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem main : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (i : LocT B), IsLocalRing (TOf B i) := by
  intro R H what₂ B hs hd i
  have := xFin_of hs hd i
  have := xNe_of hs hd i
  refine isLocalRing_of_congr (TOf B i) fun f hf x y => ?_
  rw [← Ideal.Quotient.eq]
  unfold TOf at hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    obtain ⟨v, k, hvk, rfl⟩ := hf
    refine Ideal.Quotient.eq.2 ?_
    simp only [hTfun, dif_pos hvk]
    exact sub_mem_of_ker_eq x.1 y.1 (x.2.1.trans y.2.1.symm) _
  | algebraMap r => rfl
  | add f g _ _ hf hg => simp only [Pi.add_apply, map_add, hf, hg]
  | mul f g _ _ hf hg => simp only [Pi.mul_apply, map_mul, hf, hg]

end GlobalTheory.HeckeLocN.TLocal
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localisation_heckeRing_isLocalRing : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (i : LocT B), IsLocalRing (TOf B i) := by
  atlas_forward_decl GlobalTheory.HeckeLocN.TLocal.main
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem exists_preimage_comb {K L V W : Type} [Field K] [Field L] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module L W]
    (σ : K →+* L) (f : V →ₛₗ[σ] W) (hf : Function.Injective f) (S : Finset W) (hS : ∀ y ∈ S, y ∈ Set.range f)
    (c : W → K) (x : V) (hx : f x = ∑ g ∈ S, σ (c g) • g) :
    ∃ F : Finset V, (↑F ⊆ {x : V | f x ∈ S}) ∧ x = ∑ y ∈ F, c (f y) • y := by
  classical
  refine ⟨S.preimage f hf.injOn, fun y hy => by simpa using hy, hf ?_⟩
  rw [hx, map_sum]
  simp only [LinearMap.map_smulₛₗ]
  exact (Finset.sum_preimage f S hf.injOn (fun g => σ (c g) • g) (fun g hg hn => absurd (hS g hg) hn)).symm

theorem heckeIntTw_base : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  intro D M C hR X hS tup hI hsp j w h1 h2 hw v k hg x hx
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨s, ϖ, hc, hu⟩ := hsp v hg.1
  obtain ⟨c, hc0, he⟩ := hI.int w ⟨j', by omega⟩ v k s ϖ hw hg hc hu _ hx
  have h3 := hLC_spec (mt0 M) C.Q hR (j' + 1) w v k h1 h2 hg s ϖ hc hu x
  have h4 := (M (D.what₂.muTw w) (j' + 1) h1 h2).real_inj (h3.trans he)
  obtain ⟨F, hF, hsum⟩ := exists_preimage_comb D.what₂.embLL (D.what₂.jMt (D.what₂.muTw w) (j' + 1))
    (LatticeFinitenessFree.jMt_injective _ _) _ (D.what₂.MtLat_sub _ _) c _ h4
  exact ⟨F, fun y => c (D.what₂.jMt (D.what₂.muTw w) (j' + 1) y), hF, fun y _ => hc0 _, hsum⟩

end GlobalTheory.HeckeLocN
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places : ∀ (D : D7) (M : MtFam D) (C : NChoice D) (hR : HeckeLift0 (mt0 M) C.Q) (X : CoefIn D.what₂) (hS : SplitK (mt0 M) C.Q hR X) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), MtInput D M tup C.Q → (∀ v : PlE D.host, IsSplitPl D.host v → ∃ (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E)), IsConjPl D.host v s.w ∧ IsUnif D.host.E s.v ϖ) → HeckeIntTw (base M C hR X hS) := by
  atlas_forward_decl GlobalTheory.HeckeLocN.heckeIntTw_base
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

namespace GlobalTheory.HeckeLocN

theorem actHK_holds {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B)
    (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)) : ActHK B hs hd hL hAct := by
  intro i v k hg z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c m =>
    rw [LinearMap.baseChange_tmul]
    have hs1 := ((hAct i).choose_spec.2 v k hg m)
    have e : ∀ m' : MtSub B (partCompl_of hs hd) i, PsiC B (partCompl_of hs hd) hL i (c ⊗ₜ m') = c • ((m' : partOf B i) : B.V (jOf B i) (wOf B i)) := by
      intro m'
      haveI := hL i
      simp only [PsiC, mtEquiv, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.coe_subtype]
      rw [IsBaseChange.equiv_tmul]
      rfl
    rw [e, e, map_smul]
    congr 1

end GlobalTheory.HeckeLocN
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeRing_acts_on_lattice_as_operators : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (B : LocBase0 H what₂) (hs : HeckeStd0 B) (hd : FinDimV B) (hL : MtLoc B (partCompl_of hs hd)) (hAct : ActEx B (partCompl_of hs hd)), ActHK B hs hd hL hAct := by
  atlas_forward_decl GlobalTheory.HeckeLocN.actHK_holds
end

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.TwistRamLoc

def Disc (M : Type) : Type := M

instance (M : Type) [CommGroup M] : CommGroup (Disc M) := ‹CommGroup M›
instance (M : Type) : TopologicalSpace (Disc M) := ⊥
instance (M : Type) : DiscreteTopology (Disc M) := ⟨rfl⟩
instance (M : Type) [CommGroup M] : IsTopologicalGroup (Disc M) := inferInstance

theorem finite_placesOver (E : Type) [Field E] [NumberField E] (l : ℕ) (hl : l ≠ 0) :
    (placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

end GlobalTheory.TwistRamLoc

namespace GlobalTheory.TwistRamLoc

theorem twist_ram_and_trivial_at_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  intro D cf C tp w hGAR _ hTied hTw hVal hAdm
  classical
  haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
  obtain ⟨art, ha⟩ := hGAR D.host.E D.nd.Om
  obtain ⟨ι⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex (D.what₂.places.resChar w)
  have hP : IsPsi (D.what₂.places.resChar w) (C.Q w) (tp.psi w) := tp.psi_is w hTw
  obtain ⟨a, hord⟩ := hP.ord
  have hm : 0 < D.what₂.places.resChar w ^ a := pow_pos (D.what₂.places.resChar_prime w).pos a
  obtain ⟨r, hr, hL⟩ :=
    GlobalTheory.HeckeGal.IsGlobalArtin.exists_isLAdicOf ha ι (GlobalTheory.HeckeGal.isAlgPos_zero_of_orderDvd hm hord)
  set Ψ := (C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)) with hΨ
  let φ : D.ntw.Ok (C.twI w) (C.k' w) →+* FractionRing (C.Oe w) :=
    (algebraMap (C.Oe w) (FractionRing (C.Oe w))).comp (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w))
  have hφ : Function.Injective φ :=
    (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))).comp (C.Oe_inj w)
  let Γ : Subgroup ((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) :=
    { carrier := {p | ∃ y : D.what₂.LL, ((p.1 : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) =
          ι.symm (D.what₂.embLL y) ∧ φ (p.2 : D.ntw.Ok (C.twI w) (C.k' w)) = C.embW w y}
      mul_mem' := by
        rintro p q ⟨y, h1, h2⟩ ⟨y', h1', h2'⟩
        exact ⟨y * y', by simp [h1, h1'], by simp [h2, h2']⟩
      one_mem' := ⟨1, by simp, by simp⟩
      inv_mem' := by
        rintro p ⟨y, h1, h2⟩
        refine ⟨y⁻¹, ?_, ?_⟩
        · rw [Prod.fst_inv, Units.val_inv_eq_inv_val, h1, map_inv₀, map_inv₀]
        · rw [Prod.snd_inv, map_units_inv φ, h2, map_inv₀] }
  let Φ : G D.host.E D.nd.Om →* Disc (((Qbar (D.what₂.places.resChar w))ˣ × (D.ntw.Ok (C.twI w) (C.k' w))ˣ) ⧸ Γ) :=
    (QuotientGroup.mk' Γ).comp (r.prod Ψ)
  have hrm : ∀ g, r g ^ (D.what₂.places.resChar w ^ a) = 1 := fun g => by
    have := DFunLike.congr_fun (hL.pow_eq_one ha.quot.surjective hord) g
    rwa [MonoidHom.pow_apply] at this
  have hro : IsOpen (r.ker : Set (G D.host.E D.nd.Om)) := GlobalTheory.HeckeGal.isOpen_ker_of_pow r hr hm hrm
  have hΨo : IsOpen (Ψ.ker : Set (G D.host.E D.nd.Om)) := hAdm.2.2.1
  have hΦc : Continuous Φ := by
    refine GlobalTheory.HeckeGal.continuous_of_isOpen_ker' Φ (Subgroup.isOpen_mono (H₁ := r.ker ⊓ Ψ.ker) ?_ ?_)
    · intro g hg
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at hg
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk' Γ (r g, Ψ g) = 1
      rw [hg.1, hg.2]
      exact map_one _
    · rw [Subgroup.coe_inf]
      exact hro.inter hΨo
  let S : Finset (HeightOneSpectrum (𝓞 D.host.E)) :=
    C.Q w ∪ (finite_placesOver D.host.E (D.what₂.places.resChar w) (D.what₂.places.resChar_prime w).ne_zero).toFinset
  have hΦ1 : Φ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_frob D.host.E D.nd.Om art ha _ Φ hΦc S fun v hv A hA σ hσ => ?_
    have hvQ : v ∉ C.Q w := fun h => hv (Finset.mem_union_left _ h)
    have hvl : v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun h =>
      hv (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h))
    have hu : (tp.psi w).UnrAt v := (hP.ram v).2 hvQ
    obtain ⟨y0, hy0⟩ := hVal v hu
    have hy0' : D.what₂.embLL y0 = (((tp.psi w).val v : ℂˣ) : ℂ) := by simpa [HChar.valTw] using hy0
    have hy : D.what₂.embLL y0⁻¹ = (((tp.psi w).val v)⁻¹ : ℂˣ).1 := by
      rw [map_inv₀, hy0', Units.val_inv_eq_inv_val]
    have h2 := hTied w hTw v hvQ hvl A σ hA hσ y0⁻¹ hy
    have h1 := hL.frob_unr ha (Or.inr rfl) hu hA hσ
    show QuotientGroup.mk' Γ (r σ, Ψ σ) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    refine ⟨y0⁻¹, ?_, h2.symm⟩
    show ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _
    rw [h1, map_inv₀, hy0', map_inv₀]
  have hmem : ∀ σ, (r σ, Ψ σ) ∈ Γ := fun σ => by
    have := DFunLike.congr_fun hΦ1 σ
    exact (QuotientGroup.eq_one_iff _).1 this
  have key : ∀ σ, r σ = 1 ↔ Ψ σ = 1 := fun σ => by
    obtain ⟨y, h1, h2⟩ := hmem σ
    constructor
    · intro h
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h, Units.val_one, eq_comm, map_eq_one_iff _ ι.symm.injective,
        map_eq_one_iff _ D.what₂.embLL.injective] at h1
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h1, map_one, ← map_one φ] at h2
      exact Units.ext (hφ h2)
    · intro h
      change φ (Ψ σ : D.ntw.Ok (C.twI w) (C.k' w)) = _ at h2
      rw [h, Units.val_one, map_one, eq_comm, map_eq_one_iff _ (C.embW w).injective] at h2
      change ((r σ : (Qbar (D.what₂.places.resChar w))ˣ) : Qbar (D.what₂.places.resChar w)) = _ at h1
      rw [h2, map_one, map_one] at h1
      exact Units.ext h1
  refine ⟨fun v hv A hA => ?_, fun v hv A hA σ hσ => ?_⟩
  · have hnu : ¬ (tp.psi w).UnrAt v := fun h => (hP.ram v).1 h hv
    rw [← hL.unr_iff ha (Or.inr rfl) hA] at hnu
    push_neg at hnu
    obtain ⟨σ, hσ, hne⟩ := hnu
    exact ⟨σ, hσ, fun h => hne ((key σ).2 h)⟩
  · have hloc : (tp.psi w).loc v = 1 := MonoidHom.ext (hP.atl v hv)
    exact (key σ).1 (((hL.dec_triv ha hr (Or.inr rfl) hA).2 hloc) σ hσ)

end GlobalTheory.TwistRamLoc
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l : ∀ (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (w : D.what₂.places.Pl), GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.RowTie.ChebSplit D.nd → PsiChoiceCompatible D cf C tp → TwistedAt D w → (tp.psi w).ValuesIn 0 D.what₂.embLL → NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) → (∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) ∧ (∀ v ∈ placesOver D.host.E (D.what₂.places.resChar w), ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∀ σ ∈ Dec (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ = 1) := by
  atlas_forward_decl GlobalTheory.TwistRamLoc.twist_ram_and_trivial_at_l
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

noncomputable section

namespace GlobalTheory.HeckeLocN

set_option synthInstance.maxHeartbeats 400000

def feSup {l : ℕ} [Fact l.Prime] (K L : Loc.FinExt l) : Loc.FinExt l :=
  ⟨K.1 ⊔ L.1, haveI := K.2; haveI := L.2; IntermediateField.finiteDimensional_sup _ _⟩

theorem osInt (D : D7) (B : LocBase0 D.host D.what₂) : OsInt B := fun j w y =>
  IsIntegrallyClosed.isIntegral_iff.1 <| by
    obtain ⟨p, hp, h0⟩ := D.O_int y
    refine ⟨p.map (Int.castRingHom _), hp.map _, ?_⟩
    rw [eval₂_map, Subsingleton.elim (RingHom.comp _ _) ((B.ec j w).comp (algebraMap ℤ D.what₂.LL)), ← hom_eval₂, h0, map_zero]

theorem plGwDisj (D : D7) : PlGwDisj D := by
  have key : ∀ v v', D.naut.plGw 0 v ≠ D.naut.plGw 1 v' := fun v v' e => by
    have h0 : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 0 v).asIdeal := D.naut.plGw_over 0 v
    have h1 : ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw 1 v').asIdeal := D.naut.plGw_over 1 v'
    rw [← e] at h1
    obtain ⟨a, b, hab⟩ : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne).cast
    exact (D.naut.plGw 0 v).isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ add_mem (Ideal.mul_mem_left _ _ h0) (Ideal.mul_mem_left _ _ h1)))
  intro k k' v v' e
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd e (key v v')
  · exact absurd e.symm (key v' v)
  · rfl

section Psi

variable {D : D7} {C : NChoice D} {X : CoefIn D.what₂} {ψ0 : D.what₂.places.Pl → (G D.host.E D.nd.Om →* (D.what₂.LL)ˣ)}
  (hψ0 : ∀ w g, C.embW w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) =
    algebraMap (C.Oe w) (FractionRing (C.Oe w)) (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)
      ((C.psi' w (D.ntw.art (C.twI w) (C.Q w) g) : (D.ntw.Ok (C.twI w) (C.k' w))ˣ) : D.ntw.Ok (C.twI w) (C.k' w))))
  (hP : PsiInt X ψ0) (j : ℕ) (w : D.what₂.places.Pl)

theorem psN_spec (g : G D.host.E D.nd.Om) : algebraMap (OcC X j w) (FractionRing (OcC X j w)) (psN X ψ0 hP j w g : OcC X j w) =
    ecC X j w ((ψ0 w g : (D.what₂.LL)ˣ) : D.what₂.LL) :=
  unitsLift_spec ((Units.map (ecC X j w).toMonoidHom).comp (ψ0 w)) (hP j w) g

include hψ0 in

theorem psN_eq_one (g : G D.host.E D.nd.Om) : psN X ψ0 hP j w g = 1 ↔ ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) g = 1 := by
  rw [← Units.val_eq_one, ← map_eq_one_iff _ (IsFractionRing.injective (OcC X j w) (FractionRing (OcC X j w))), psN_spec,
    map_eq_one_iff _ (ecC X j w).injective, ← map_eq_one_iff _ (C.embW w).injective, hψ0,
    map_eq_one_iff _ (IsFractionRing.injective (C.Oe w) (FractionRing (C.Oe w))), map_eq_one_iff _ (C.Oe_inj w),
    Units.val_eq_one]
  rfl

include hψ0 in
theorem psN_of_art {g : G D.host.E D.nd.Om} (h : D.ntw.art (C.twI w) (C.Q w) g = 1) : psN X ψ0 hP j w g = 1 := by
  rw [psN_eq_one hψ0, MonoidHom.comp_apply, h, map_one]

include hψ0 in
theorem psN_ord (g : G D.host.E D.nd.Om) : ∃ n : ℕ, psN X ψ0 hP j w g ^ (D.what₂.places.resChar w ^ n) = 1 := by
  obtain ⟨n, hn⟩ := D.ntw.RCG_l _ _ (D.ntw.art (C.twI w) (C.Q w) g)
  rw [C.twI_l, ← map_pow] at hn
  exact ⟨n, by rw [← map_pow]; exact psN_of_art hψ0 hP j w hn⟩

include hψ0 in
theorem psN_open : IsOpen ((psN X ψ0 hP j w).ker : Set (G D.host.E D.nd.Om)) :=
  Subgroup.isOpen_mono (H₁ := (D.ntw.art (C.twI w) (C.Q w)).ker) (fun _ hg => psN_of_art hψ0 hP j w hg) (D.ntw.art_cont _ _)

include hψ0 in
theorem psN_anti : AntiHom D.ntw.cc (psN X ψ0 hP j w) := fun g g' h => by
  rw [eq_inv_iff_mul_eq_one, ← map_mul]
  exact psN_of_art hψ0 hP j w (by rw [map_mul, D.ntw.art_anti _ _ g g' h, inv_mul_cancel])

include hψ0 in
theorem psN_ram (h : ∀ v ∈ C.Q w, ∀ A : ValuationSubring D.nd.Om, IsPlaceOver A v → ∃ σ ∈ Ine (F := D.host.E) A, ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) σ ≠ 1) :
    RamExactly (psN X ψ0 hP j w) (↑(C.Q w) : Set (HeightOneSpectrum (𝓞 D.host.E))) := fun v A hA => by
  constructor
  · rintro ⟨σ, hσ, hne⟩
    by_contra hv
    exact hne (psN_of_art hψ0 hP j w (D.ntw.art_unr _ _ v hv A hA σ hσ))
  · intro hv
    obtain ⟨σ, hσ, hne⟩ := h v hv A hA
    exact ⟨σ, hσ, fun e => hne ((psN_eq_one hψ0 hP j w σ).1 e)⟩

end Psi

set_option maxHeartbeats 2000000 in

theorem ndSpec_exists : GlobalTheory.Published.GlobalArtinReciprocity → HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → (Function.Injective D.what₂.OtoLL ∧ ∃ F : Subfield D.what₂.LL, ∀ x, x ∈ D.what₂.OtoLL.range ↔ x ∈ F ∧ IsIntegral ℤ x) → (∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) → ∀ big : D.what₂.places.Pl → Finset ℂ, ∃ (X : LocNd (lay0 D)) (T : LocTw X), Nonempty (NdSpec A.pl M C big X T) := by
  intro hArt hStd D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI _ _ hpd hCheb hOS hVal big
  obtain ⟨hO, hc⟩ := GlobalTheory.T.twistConductors_over_real_places_and_conj_stable D cf C tp hCS.off
  have hG := GlobalTheory.T.heckeGeneratorPlacesOutsideLevel_of_stable D cf M C tp hMI hO
  have hX := GlobalTheory.T.exists_conjugate_splitPlace_and_uniformizer D
  have hR := GlobalTheory.T.exists_coefficientLinear_lift_doubleCosetOperators D M C tp.tup hStd hG hMI
  have hCm := GlobalTheory.T.liftedHeckeOperators_at_generators_commute D M C hR hStd hG hX
  choose F1 hF1 using GlobalTheory.T.exists_padicFiniteExt_containing_all_hecke_eigenvalues D M C hR (plEmb A.pl) hCm
  choose F2 hF2 hF2' using GlobalTheory.T.exists_padicFiniteExt_containing_coeffField_and_numbers D A.pl big
  choose F3 hF3 using GlobalTheory.T.localBridges_at_placesOverResidueChar_of_large_coeff D
  choose F4 hF4 using GlobalTheory.T.exists_twist_ring_map_large_coefficient_rings D C Bs.twF low (plEmb A.pl) Bs.tw hCS.choice
  obtain ⟨X, hXE, h1, h2, h3, h4⟩ : ∃ X : CoefIn D.what₂, X.E = plEmb A.pl ∧ (∀ j w, (F1 j w).1 ≤ (X.Kx j w).1) ∧
      (∀ j w, (F2 w).1 ≤ (X.Kx j w).1) ∧ (∀ j w, (F3 w).1 ≤ (X.Kx j w).1) ∧ ∀ j w, (F4 w).1 ≤ (X.Kx j w).1 :=
    ⟨coefIn A.pl (fun j w => feSup (feSup (F1 j w) (F2 w)) (feSup (F3 w) (F4 w)))
      (fun j w x => (le_sup_of_le_left le_sup_right : (F2 w).1 ≤ ((F1 j w).1 ⊔ (F2 w).1) ⊔ ((F3 w).1 ⊔ (F4 w).1)) (hF2 w x)), rfl,
      fun _ _ => le_sup_of_le_left le_sup_left, fun _ _ => le_sup_of_le_left le_sup_right,
      fun _ _ => le_sup_of_le_right le_sup_left, fun _ _ => le_sup_of_le_right le_sup_right⟩
  have hS : SplitK (mt0 M) C.Q hR X := fun j w => hF1 j w X hXE (h1 j w)
  choose twC hTwA hTwR hTwE using fun j w => hF4 w X j hXE (h4 j w)
  obtain ⟨ψ0, -, hψ0, -⟩ := hCS.nct.psi_eq
  have hP := GlobalTheory.T.twistCharacterValues_integral_units_at_place D C X ψ0 hψ0
  have hs := GlobalTheory.T.heckeStandardFacts_on_localisation_base D M C hR X hS hStd hG hX hCm
  have hd := GlobalTheory.T.finiteDimensional_localisation_space_all (base M C hR X hS)
  have hML := LatticeFinitenessFree.mtLoc_holds (partCompl_of hs hd)
  have hAct := GlobalTheory.T.heckeRing_acts_faithfully_on_localisedLattice _ hs hd hML (GlobalTheory.T.heckeOperator_integral_on_lattice_at_twisted_places D M C hR X hS tp.tup hMI hX)
    (GlobalTheory.T.heckeOperators_on_localisation_space_semisimple D M C hR X hS hStd GlobalTheory.T.splitPlace_doubleCosetOperator_semisimple_typeSpace hG hX)
  have hAHK := GlobalTheory.T.heckeRing_acts_on_lattice_as_operators _ hs hd hML hAct
  have hI := osInt D (base M C hR X hS)
  have hGal := fun w (hw : TwistedAt D w) => GlobalTheory.T.twistCharacter_ramified_at_conductor_trivial_above_l D cf C tp w hArt hCheb hCS.psi hw (hVal w hw) (hCS.adm w hw)
  have htw : ∀ w v, v ∈ C.Q w → TwistedAt D w := fun w v hv => by
    by_contra hw
    rw [hCS.off w hw] at hv
    exact absurd hv (Finset.notMem_empty v)
  have hQl : ∀ w v, v ∈ C.Q w → v ∉ placesOver D.host.E (D.what₂.places.resChar w) := fun w v hv =>
    C.twI_l w ▸ ((hCS.adm w (htw w v hv)).1 v hv).2
  have hQS : ∀ w v, v ∈ C.Q w → v ∉ exceptionalPlaces D.host (D.what₂.places.resChar w) := fun w v hv h => by
    have ha := (hCS.adm w (htw w v hv)).2.1 v hv
    rcases h.1 with h | h | h
    · exact ha.2 0 h
    · exact ha.2 1 h
    · refine ha.1 (Finset.mem_coe.1 ?_)
      rw [D.ntw.pD_eq, C.twI_l]
      exact h
  have hSs : ∀ l v, v ∈ exceptionalPlaces D.host l → IsSplitPl D.host v := fun l v h => by
    rcases h.1 with h | h | h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 0 v h
    · exact GlobalTheory.T.typePrime_places_isSplitPlace D 1 v h
    · split_ifs at h
      · exact hpd v (Or.inr h)
      · exact hpd v (Or.inl h)
  have hRP := fun j w (hw : TwistedAt D w) => psN_ram hψ0 hP j w (hGal w hw).1
  refine ⟨_, _, nonempty_spec (base M C hR X hS) C hs hd hML (LatticeFinitenessFree.mtSub_free _) (LatticeFinitenessFree.mtSub_finite _) (GlobalTheory.T.localisation_heckeRing_isLocalRing _ hs hd) hAct
    (GlobalTheory.T.heckeEigenspace_ne_bot_every_localisation_point _ hs hd hML hAct hAHK) (fun i => twC (jOf _ i) (wOf _ i)) (fun i => psN X ψ0 hP (jOf _ i) (wOf _ i))
    (GlobalTheory.T.localisation_galoisCharacter_continuous D M C hR X hS twC ψ0 hP hTwA (psN_open hψ0 hP))
    (fun i v hv => hv.elim (fun h => hSs _ v ((Set.Finite.mem_toFinset _).1 h))
      (fun h => ((hCS.adm _ (htw _ v h)).1 v h).1))
    (fun i => Finset.disjoint_left.2 fun v h h' => hQS _ v h' ((Set.Finite.mem_toFinset _).1 h)) hQl ?_ hI
    (GlobalTheory.T.latticeBaseChange_free_over_localisation_coeffRing D _ hI hOS) (fun a => hTwE _ _ a.2.2.2.2.2) (fun a => psN_ord hψ0 hP _ _) (fun a => psN_open hψ0 hP _ _)
    (fun a => psN_anti hψ0 hP _ _) (fun a => hRP _ _ a.2.2.2.2.2)
    (fun a v hv B hB σ hσ => (psN_eq_one hψ0 hP _ _ σ).2 ((hGal _ a.2.2.2.2.2).2 v hv B hB σ hσ))
    A.pl M big (fun j w h1 h2 v k s ϖ hg hcj hu x => hLC_spec (mt0 M) C.Q hR j w v k h1 h2 hg s ϖ hcj hu x) hO hc
    (fun _ => rfl) (iqC X) (fun j w z => (iqC_alg X j w _).trans rfl) ?_ ?_ hAHK (plGwDisj D) ?_ (fun a => hTwA _ _)
    (fun a => hTwR _ _) (fun j w => hF3 w X j (h3 j w))⟩
  · intro i v hv
    have hw : TwistedAt D (wOf _ i) := i.2.2.2.2.2
    obtain ⟨σ, hσ, hne⟩ := (hRP (jOf _ i) _ hw v _ (D.nd.plOm.2 v)).2 hv
    have ha := hCS.adm _ hw
    have h1 := D.ntw.twistCharacterFamily_unramified (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) v (ha.1 v hv).2 (ha.2.1 v hv).2 (ha.2.1 v hv).1 _
      (D.nd.plOm.2 v) σ hσ
    refine ⟨σ, hσ, fun e => hne ?_⟩
    have e' : Units.map (twC (jOf _ i) (wOf _ i)).toMonoidHom (D.ntw.chi1 (C.twI (wOf _ i)) (jOf _ i) (C.sd (wOf _ i)) σ) *
        psN X ψ0 hP (jOf _ i) (wOf _ i) σ = 1 := e
    rwa [h1, map_one, one_mul] at e'
  · intro j w x
    change A.pl.ι w (iqC X j w (ecC X j w x)) = _
    rw [iqC_ec, hXE]
    exact (A.pl.ι w).apply_symm_apply _
  · intro j w z hz
    obtain ⟨x, hx⟩ := iqC_surj X j w _ (h2 j w (hF2' w z hz))
    exact ⟨x, (congrArg (A.pl.ι w) hx).trans ((A.pl.ι w).apply_symm_apply z)⟩
  · intro a g y hy
    obtain rfl := (C.embW _).injective (hy.trans (hψ0 _ g).symm)
    exact (psN_spec hP _ _ g).symm

end GlobalTheory.HeckeLocN
end
end
