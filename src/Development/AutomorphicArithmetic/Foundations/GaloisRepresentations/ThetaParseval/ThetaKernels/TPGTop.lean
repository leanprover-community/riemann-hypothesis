import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.MemClosureOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsNe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ProjEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.AbsIso
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelLocalOperatorAction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKernelFundamentalProperties
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieSecondOrderOfRealLift
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine
import Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
import Development.WeilBound.ThetaLifts.LatticeBasics.LocUnrSplit
import Development.WeilBound.ThetaLifts.LatticeBasics.PresDOf
import Development.WeilBound.ThetaLifts.LatticeBasics.PairsFin
import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstFin
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
import Development.WeilBound.ThetaLifts.LatticeBasics.ConstOfGood
import Development.WeilBound.ThetaLifts.LatticeBasics.OrthAn
import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpen
import Development.WeilBound.ThetaLifts.LatticeBasics.HeightGLLe
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStd
import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwo
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairExistence.WeilEx
import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
import Development.WeilBound.ThetaLifts.Reductions.LocalLift
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsLinearFunctionalAtSplitPlace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.WeilBound.ThetaLifts.LatticeBasics.NormZeta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsEDetUnitary
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGRealPair
import Development.AutomorphicArithmetic.AdelicQuotients.MatrixCoefficientBoundedByValueAtOne
import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryAdelicMemOfLocalGroupsNearOne
import Development.AutomorphicArithmetic.AdelicQuotients.UnitaryLocalGroupLeOffPlacesEmpty
import Development.AutomorphicArithmetic.AdelicQuotients.HaarMeasureTripleProductDecomposition
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SchurStep
import Development.WeilBound.ThetaLifts.LatticeBasics.BadFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleEqZeroOfComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterUnramifiedAlmostAllPlaces
import Development.WeilBound.ThetaLifts.LatticeBasics.BotAsm
import GroundTheory.AutomorphicForms.GL2.InnerProductParamHolo
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDecomp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGBumpAny
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.IntOfOff
import Development.AutomorphicArithmetic.AdelicQuotients.RieszRepresentationSesquilinear
import Development.AutomorphicArithmetic.AdelicQuotients.MeasurableOfSeparatingFunctionals
import Development.AutomorphicArithmetic.AdelicQuotients.InnerProductIntegralFundamentalDomainOfCompact
import Development.AutomorphicArithmetic.AdelicQuotients.IrreducibleHermitianFormUnique
import Development.WeilBound.ThetaLifts.LatticeBasics.ThetaBox
import Development.WeilBound.ThetaLifts.LocalTheory.ArchimedeanBumps.ArchHeisOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGLiftAut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ReadLift

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl
namespace UpperTheory.TP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private theorem hgt_swap_pk (hJ : X.J.det ≠ 0) {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a)
    {e : UA σ X.J × UA σ X.J →* G2 σ X} (he : ∀ g g', IsEmb g g' (e (g, g'))) (g : UA σ X.J) :
    a (e (g, 1)) = a (e (1, g⁻¹)) := by
  have hp : IsPar (e (g, g)) (g : GL (Fin n) (AE F E)) := by
    change mat2 (e (g, g)) * diagCols (E := AE F E) (Fin n) = diagCols (E := AE F E) (Fin n) * mat g
    rw [he, diagCols, Matrix.fromRows_mul, Matrix.fromBlocks_mul_fromRows]
    simp
  have e1 : e (g, 1) = e (g, g) * e (1, g⁻¹) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel]
  rw [e1, ha.mul hp, GlobalTheory.WeilEx.Jac.absE_det_unitary hJ g]
  simp
end UpperTheory.TP
theorem UpperTheory.TP.hgtFst_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.HgtFst_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he
  have cX := T.cpt F E σ B n X n 0 hB (.inl hX) (by simp)
  haveI := cX.lc
  haveI := cX.sc
  obtain ⟨μ₀, D, hμ₀, -⟩ := cX.ex
  obtain ⟨t₀, ht₀⟩ := _root_.GlobalTheory.ThK.Dbl.hgtInt_of_k T.stab2 F E σ B n X n 0 hB (.inl hX) K a e hK ha he μ₀ hμ₀
  refine ⟨t₀, fun μ hμ t ht => ?_⟩
  haveI := hμ
  haveI := hμ₀
  haveI := cX.right μ hμ
  have hJ : X.J.det ≠ 0 := GlobalTheory.ThK.Dbl.Hgt.det_ne (.inl hX)
  have h1 : Integrable (fun g => a (e (1, g)) ^ t) μ := by
    rw [Measure.isMulLeftInvariant_eq_smul μ μ₀]
    exact (ht₀ t ht).smul_measure ENNReal.coe_ne_top
  obtain ⟨c, -, hc⟩ := inv_scale μ
  have h2 : Integrable (fun g => ((a (e (g, 1)) ^ t : ℝ) : ℂ)) μ := (hc _).1 (by
    simp only [UpperTheory.TP.hgt_swap_pk hJ ha he, inv_inv]
    exact h1.ofReal)
  simpa using h2.re
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
section SlopeTestRemainingChoices
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n}
private def fixG_pk {R : Type} [Ring R] (σ : E →ₐ[F] E) (X : Spc F E n) (f : AE F E →+* R) : Subgroup (UA σ X.J) where
  carrier := {g | (mat g).map f = 1}
  one_mem' := Matrix.map_one f (map_zero _) (map_one _)
  mul_mem' := fun {a b} ha hb => by
    show (mat (a * b)).map f = 1
    rw [Euler.mm, Matrix.map_mul]
    exact (congrArg₂ (· * ·) ha hb).trans (mul_one _)
  inv_mem' := fun {a} ha => by
    have e : (mat a⁻¹).map f * (mat a).map f = 1 := by
      rw [← Matrix.map_mul, ← Euler.mm, inv_mul_cancel]
      exact Matrix.map_one f (map_zero _) (map_one _)
    rw [show (mat a).map f = 1 from ha, mul_one] at e
    exact e
private theorem gOff_parts_pk {S : Finset (Pl F)} {c : UA σ X.J} (h : c ∈ gOff σ X S) :
    (∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1) ∧ ∀ v ∈ S, OffAt v c := by
  constructor
  · intro w
    have : gOff σ X S ≤ fixG_pk σ X (compInf F E w : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.1 w
    exact this h
  · intro v hv
    have : gOff σ X S ≤ fixG_pk σ X (compFin F E v : AE F E →+* _) :=
      (Subgroup.closure_le _).2 fun g hg => hg.2 v hv
    exact this h
private theorem eq_one_of_parts_pk {c : UA σ X.J} (h1 : ∀ w : InfinitePlace F, (mat c).map (compInf F E w) = 1)
    (h2 : ∀ v, OffAt v c) : c = 1 := by
  refine Subtype.ext (Units.ext ?_)
  show mat c = 1
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.SWOpFin.tens_eq_zero_of_comp (fun v => ?_) (fun w => ?_))
  · have e : (mat c).map (compFin F E v) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compFin F E v) := by
      rw [Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
      exact h2 v
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
  · have e : (mat c).map (compInf F E w) = (1 : Matrix (Fin n) (Fin n) (AE F E)).map (compInf F E w) := by
      rw [Matrix.map_one (compInf F E w) (map_zero _) (map_one _)]
      exact h1 w
    rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun e i) j)
end SlopeTestRemainingChoices
theorem UpperTheory.exists_finite_places_integral_mem_nhds_one :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n}, _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B n 0 → IsCompact {g : UA σ X.J | IntAll g} → (∀ S, IsClosed (gOff σ X S : Set (UA σ X.J))) → ∀ {N : Set (UA σ X.J)}, N ∈ 𝓝 (1 : UA σ X.J) → ∃ S₀ : Finset (Pl F), ∀ c ∈ gOff σ X S₀, IntAll c → c ∈ N := by
  intro F E _ _ _ _ _ σ B n X _ _ hK hC N hN
  classical
  have hs : IsCompact ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) := hK.inter_right isOpen_interior.isClosed_compl
  have anti : ∀ {S T : Finset (Pl F)}, S ⊆ T → (gOff σ X T : Set (UA σ X.J)) ⊆ gOff σ X S := fun {S T} h =>
    Subgroup.closure_mono fun g hg => ⟨hg.1, fun v hv => hg.2 v (h hv)⟩
  have hd : Directed (· ⊇ ·) (fun S : Finset (Pl F) => (gOff σ X S : Set (UA σ X.J))) := fun S T =>
    ⟨S ∪ T, anti Finset.subset_union_left, anti Finset.subset_union_right⟩
  have hi : ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ ⋂ S : Finset (Pl F), (gOff σ X S : Set (UA σ X.J)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun c hc => ?_
    have h := Set.mem_iInter.1 hc.2
    have e : c = 1 := eq_one_of_parts_pk (gOff_parts_pk (h ∅)).1
      fun v => (gOff_parts_pk (h {v})).2 v (Finset.mem_singleton_self v)
    exact hc.1.2 (e ▸ mem_interior_iff_mem_nhds.2 hN)
  obtain ⟨S, hS⟩ := hs.elim_directed_family_closed _ hC hi hd
  refine ⟨S, fun c hc hI => ?_⟩
  by_contra hn
  have hm : c ∈ ({g : UA σ X.J | IntAll g} ∩ (interior N)ᶜ) ∩ (gOff σ X S : Set (UA σ X.J)) :=
    ⟨⟨hI, fun h => hn (interior_subset h)⟩, hc⟩
  rw [hS] at hm
  exact hm
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions UpperTheory.TP
theorem UpperTheory.exists_finite_unramified_outside_of_isHecke :
    ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}, _root_.UpperTheory.TP.W.GoodK σ B → ∀ {χ : Chr F E}, IsHecke F E χ → ∃ S : Finset (Pl F), UnrOff χ (S : Set (Pl F)) := by
  intro F E _ _ _ _ _ σ B hB χ hχ
  classical
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ UnrAt χ w}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.PairVac.eventually_unrAt_of_isHecke σ hB.cm χ hχ)
  refine ⟨(hfin.image fun w => w.under (𝓞 F)).toFinset, fun w hw => ?_⟩
  by_contra hu
  exact hw (by
    show w.under (𝓞 F) ∈ (((hfin.image fun w => w.under (𝓞 F)).toFinset : Finset (Pl F)) : Set (Pl F))
    rw [Set.Finite.coe_toFinset]
    exact ⟨w, hu, rfl⟩)
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem nv_sf_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] : SFinite μ := inferInstance
end UpperTheory.TP
open UpperTheory.TP
set_option maxHeartbeats 2000000 in
theorem _root_.UpperTheory.TP.nonVan_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k → _root_.UpperTheory.TP.Decomp_k → _root_.UpperTheory.TP.BumpAny_k → _root_.UpperTheory.TP.Datum_k → _root_.UpperTheory.TP.Tail_k → UpperTheory.TP.AbsNe → _root_.UpperTheory.TP.SchurStep_k → _root_.UpperTheory.TP.NonVan_k := by
  intro T hR hD hBu hDa hTl hAb hSc E _ _ _ B n d X W M χX χW om hP hn e e' he he' hd K a ε hK ha hε t₀ ht hlt U hU f₀ hf₀ hf0 φ hφ0 hS
  classical
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA (cj E) X.J
  have hC : Cpt (cj E) X.J := T.cpt _ E (cj E) B n X n 0 hP.base (Or.inl hP.herm) (by simp)
  have hS' := hS
  have hA : GlobalTheory.UnitaryBC.IsAutFormU φ := by
    obtain ⟨V, _, _, _, ρ, i, jj, x₀, -, -, hjx, hjU, -, -⟩ := hS'
    exact hU.aut φ (hjx ▸ hjU x₀)
  set φ' : UA (cj E) X.J → ℂ := φ ∘ e.symm with hφ'
  have hfn : IsFn φ' := ⟨hA.cont.comp e.symm.continuous, fun γ hγ g => by
    have h1 : e.symm γ ∈ GlobalTheory.UnitaryBC.ratU E n := (he.rat _).1 (by simpa using hγ)
    simpa [hφ'] using hA.left _ h1 (e.symm g)⟩
  have hφ'0 : φ' ≠ 0 := fun h => hφ0 (funext fun g => by simpa [hφ'] using congrFun h (e g))
  obtain ⟨r, r0, r1, r2⟩ := UpperTheory.matrix_coefficient_bounded_by_value_at_one (M := M) hC hP.good.haar hP.good.dom hfn hφ'0
  obtain ⟨O, oO, eO⟩ := isOpen_induced_iff.1 hA.level
  have one_O : (1 : GlobalTheory.UnitaryBC.UA E n) ∈ O := by
    have : (1 : GlobalTheory.UnitaryBC.finU E n) ∈ Subtype.val ⁻¹' O := by
      rw [eO]; show GlobalTheory.UnitaryBC.RU E n 1 φ = φ; rw [map_one]; rfl
    exact this
  set N : Set (UA (cj E) X.J) := e.symm ⁻¹' O with hN
  have oN : IsOpen N := oO.preimage e.symm.continuous
  have one_N : (1 : UA (cj E) X.J) ∈ N := by simpa [hN] using one_O
  have hfix : ∀ g ∈ gOff (cj E) X ∅, g ∈ N → ∀ y, φ' (y * g) = φ' y := fun g hg hgN y => by
    have k1 : e.symm g ∈ GlobalTheory.UnitaryBC.finU E n := (he.fin _).1 (by simpa using hg)
    have k2 : (⟨e.symm g, k1⟩ : GlobalTheory.UnitaryBC.finU E n) ∈ {k : GlobalTheory.UnitaryBC.finU E n | GlobalTheory.UnitaryBC.RU E n k φ = φ} := by
      rw [← eO]; exact hgN
    have : φ (e.symm y * e.symm g) = φ (e.symm y) := congrFun k2 (e.symm y)
    simpa [hφ'] using this
  obtain ⟨⟨j0, hj0⟩, -, -, -, cK0, -, -, -, -⟩ := hD _ E (cj E) B n X hP.base hP.herm ∅
  have clOff : ∀ S, IsClosed (gOff (cj E) X S : Set (UA (cj E) X.J)) := fun S =>
    (hD _ E (cj E) B n X hP.base hP.herm S).2.2.2.1
  obtain ⟨S₀, hS₀⟩ := _root_.UpperTheory.exists_finite_places_integral_mem_nhds_one hP.base hP.herm cK0 clOff (oN.mem_nhds one_N)
  obtain ⟨R, hRam⟩ := _root_.UpperTheory.exists_finite_unramified_outside_of_isHecke hP.base hP.hW
  have hint := ht _ hlt.le
  obtain ⟨S, hSS, hTail⟩ := hTl _ E (cj E) B n X hP.base hP.herm K a ε hK ha hε M.μ ((d : ℝ) / 2) hP.good.haar hint (S₀ ∪ R)
  have hOffS : gOff (cj E) X S ≤ gOff (cj E) X S₀ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => hg.2 v (hSS (Finset.mem_union_left _ hv))⟩
  have hOff0 : gOff (cj E) X S ≤ gOff (cj E) X ∅ := Subgroup.closure_mono fun g hg =>
    ⟨hg.1, fun v hv => absurd hv (by simp)⟩
  have hunr : UnrOff χW (S : Set (Pl (maximalRealSubfield E))) := fun w hw => hRam w fun h => hw (by
    simp only [above, Set.mem_setOf_eq] at h ⊢
    exact hSS (Finset.mem_union_right _ h))
  have hbump := fun v => hBu _ E (cj E) B n d X W M χX χW om hP hn hd v N (oN.mem_nhds one_N)
  choose H b hb hHN using hbump
  set φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ :=
    fun v => if v ∈ S then b v else M.vac v with hφf
  have hfin : IsFin M φf := by
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v ∈ S
      · simpa [hφf, hv] using (hb v).1
      · simpa [hφf, hv] using (hP.good.vac v).1
    · filter_upwards [S.finite_toSet.compl_mem_cofinite] with v hv
      simp only [Set.mem_compl_iff, Finset.mem_coe] at hv
      simp [hφf, hv]
  letI : MeasurableSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF (maximalRealSubfield E)) := ⟨rfl⟩
  let ν : Measure (Fin n × Fin d → AF (maximalRealSubfield E)) := Measure.addHaar
  have hν : ν.IsAddHaarMeasure := inferInstance
  obtain ⟨hc1, hco⟩ := hDa _ E (cj E) B n d X W M χX χW om hP hn K a ε hK ha hε ν hν S hunr H φf hfin
    (fun v hv => by simpa [hφf, hv] using hb v) (fun v hv => by simp [hφf, hv]) f₀ hf₀ hf0
  obtain ⟨⟨j, hj⟩, cInf, clAt, clOff', cK, oK, -, hcomp, -⟩ := hD _ E (cj E) B n X hP.base hP.herm S
  let Tst : Subgroup (UA (cj E) X.J) :=
    { carrier := {g | ∀ y, φ' (y * g) = φ' y}
      one_mem' := fun y => by rw [mul_one]
      mul_mem' := fun {g h} hg hh y => by rw [← mul_assoc, hh, hg]
      inv_mem' := fun {g} hg y => by rw [← hg (y * g⁻¹), inv_mul_cancel_right] }
  have hHfix : (⨆ v ∈ S, H v) ≤ Tst := iSup₂_le fun v _ g hg =>
    hfix g (UpperTheory.unitaryLocalGroup_le_offPlaces_empty v ((hb v).2.2.1 hg)) (hHN v hg)
  have hcomm : ∀ (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 * c.1 = c.1 * b.1 := fun b c => by
    have h1 : j ((1, (b, 1)) * (1, (1, c))) = j ((1, (1, c)) * (1, (b, 1))) := by
      congr 1
      simp
    rw [map_mul, map_mul, hj, hj] at h1
    simpa using h1
  have hmc : ∀ (x : UA (cj E) X.J) (b : gAt (cj E) X S) (c : gOff (cj E) X S), b.1 ∈ (⨆ v ∈ S, H v) →
      mc M φ' (x * b.1 * c.1) = mc M φ' (x * c.1) := fun x b c hbH => by
    have : (fun y => φ' (y * (x * b.1 * c.1))) = fun y => φ' (y * (x * c.1)) := funext fun y => by
      rw [mul_assoc x, hcomm, ← mul_assoc x, ← mul_assoc y]
      exact hHfix hbH _
    simp only [mc, this]
  haveI : LocallyCompactSpace (gInf (cj E) X) := cInf.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gAt (cj E) X S) := clAt.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (gOff (cj E) X S) := clOff'.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let μA : Measure (gInf (cj E) X) := Measure.haar
  let μB : Measure (gAt (cj E) X S) := Measure.haar
  let μC : Measure (gOff (cj E) X S) := Measure.haar
  haveI : SFinite μA := nv_sf_pk μA
  haveI : SFinite μB := nv_sf_pk μB
  haveI : SFinite μC := nv_sf_pk μC
  obtain ⟨κ, hκ, hκe⟩ := hSc E B n d X W M χX χW om hP hn e e' he he' U hU f₀ hf0 φ hφ0 hS ν hν φf hfin μA inferInstance
  have hPol : pure f₀ φf ∈ PolData B M := Submodule.subset_span ⟨f₀, hf₀, φf, hfin.1, hfin.2, rfl⟩
  obtain ⟨hI, hZ⟩ := hR _ E (cj E) B n d X W M χX χW om hP hn (by omega) K a ε hK ha hε t₀ ht hlt ν hν _ hPol φ' hfn
  refine ⟨φf, hfin, fun h0 => ?_⟩
  obtain ⟨hIP, c, hc⟩ := UpperTheory.haarMeasure_triple_product_decomposition _ _ _ cInf.isClosed clAt clOff' j M.μ hP.good.haar μA μB μC inferInstance inferInstance
    inferInstance _ hI
  rw [hZ h0, mul_zero] at hc
  choose s s1 s2 s3 using fun c : gOff (cj E) X S => (hco 1 (one_mem _) 1 (one_mem _) c.1 c.2).2
  have oH := UpperTheory.unitaryAdelic_mem_of_localGroups_near_one S H (fun v _ => (hb v).2.2.2.2.1) hcomp
  have hIG : ∀ g ∈ (⨆ v ∈ S, H v), IntAll g := fun g hg =>
    Subgroup.mem_iInf.1 ((iSup₂_le fun v _ g hg => Subgroup.mem_iInf.2 fun w =>
      Bad.int_all ((hb v).2.2.1 hg) ((hb v).2.2.2.1 g hg) w : (⨆ v ∈ S, H v) ≤ ⨅ w, Euler.intGrp (cj E) X w) hg)
  have cB : IsCompact {b : gAt (cj E) X S | IntAll b.1} := clAt.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  have cC : IsCompact {c : gOff (cj E) X S | IntAll c.1} := clOff'.isClosedEmbedding_subtypeVal.isCompact_preimage cK
  refine hAb _ _ _ μA μB μC {b | b.1 ∈ ⨆ v ∈ S, H v} {c | IntAll c.1} oH.measurableSet
    (oK.preimage continuous_subtype_val).measurableSet (oH.measure_ne_zero μB ⟨1, one_mem (⨆ v ∈ S, H v)⟩)
    (ne_top_of_le_ne_top cB.measure_lt_top.ne (measure_mono fun b hb' => hIG _ hb')) cC.measure_lt_top.ne
    _ (fun x c => coef om ν (pure f₀ φf) x.1 * star (mc M φ' (x.1 * c.1))) s (fun c => star (mc M φ' c.1))
    (κ * coef om ν (pure f₀ φf) 1) r (fun c => ENNReal.ofReal (a (ε (c.1, 1)) ^ ((d : ℝ) / 2)))
    (mul_ne_zero hκ hc1) r0 hIP ?_ ?_ ?_ ?_ ?_ (hTail μC inferInstance) hc
  · intro x b c hb'
    rw [hj]
    rw [(hco x.1 x.2 b.1 b.2 c.1 c.2).1 hb', zero_mul]
  · intro x c b hb'
    rw [hj]
    simp only
    rw [s3 c x.1 x.2 b.1 hb', hmc _ _ _ hb', mul_assoc]
  · intro c
    exact hκe c.1 (hOff0 c.2)
  · intro c hc'
    refine ⟨s2 c hc', ?_⟩
    have : (fun y => φ' (y * c.1)) = fun y => φ' (y * 1) := funext fun y => by
      rw [mul_one]; exact hfix _ (hOff0 c.2) (hS₀ _ (hOffS c.2) hc') y
    have e1 : mc M φ' c.1 = r := by rw [← r1]; simp only [mc, this]
    simp [e1]
  · intro c
    refine ⟨by simpa using r2 c.1, ?_⟩
    rw [← s1 c, ofReal_norm_eq_enorm]
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem zero_of_half_pk {U : Set ℂ} (hU : IsOpen U) (hd : ∀ z : ℂ, ∀ᶠ z' in 𝓝[≠] z, z' ∈ U) {τ : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U ∩ {z | τ < z.re})) {t : ℝ} (ht : ∀ z : ℂ, t < z.re → z ∈ U ∧ f z = 0) {s : ℂ} (hs : s ∈ U)
    (hs' : τ < s.re) : f s = 0 := by
  have hsh : Continuous fun z : ℂ => z + (τ : ℂ) := by fun_prop
  have key := eq_zero_of_right (U := (fun z : ℂ => z + (τ : ℂ)) ⁻¹' U) (hU.preimage hsh)
    (fun z => by
      have tt : Tendsto (fun z : ℂ => z + (τ : ℂ)) (𝓝[≠] z) (𝓝[≠] (z + (τ : ℂ))) :=
        tendsto_nhdsWithin_iff.2 ⟨hsh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          eventually_mem_nhdsWithin.mono fun w hw h => hw (add_right_cancel h)⟩
      exact tt.eventually (hd _))
    (f := fun z => f (z + (τ : ℂ)))
    (hf.comp (by fun_prop) fun z hz => ⟨hz.1, by simpa using hz.2⟩)
    (t := t - τ) (fun z hz => ⟨(ht _ (by simp; linarith [show t - τ < z.re from hz])).1,
      (ht _ (by simp; linarith [show t - τ < z.re from hz])).2⟩)
    (s := s - (τ : ℂ)) (by simpa using hs) (by simpa using hs')
  simpa using key
private theorem cpow_integral_pk {Y : Type} [MeasurableSpace Y] {μ : Measure Y} {A : Y → ℝ} {b : Y → ℂ} {t₀ q C : ℝ}
    (h0 : ∀ x, 0 < A x) (mA : Measurable A) (mb : AEStronglyMeasurable b μ) (hb : ∀ x, ‖b x‖ ≤ C * A x ^ q)
    (hi : ∀ t, t₀ ≤ t → Integrable (fun x => A x ^ t) μ) (s₀ : ℂ) :
    (∀ z : ℂ, t₀ < z.re - s₀.re + q → Integrable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ) ∧
      DifferentiableOn ℂ (fun z => ∫ x, (A x : ℂ) ^ (z - s₀) * b x ∂μ) {z : ℂ | t₀ < z.re - s₀.re + q} := by
  have mz : ∀ z : ℂ, AEStronglyMeasurable (fun x => (A x : ℂ) ^ (z - s₀) * b x) μ := fun z =>
    ((Complex.measurable_ofReal.comp mA).pow_const _).aestronglyMeasurable.mul mb
  have nz : ∀ (z : ℂ) x, ‖(A x : ℂ) ^ (z - s₀) * b x‖ ≤ |C| * A x ^ (z.re - s₀.re + q) := fun z x => by
    have p := h0 x
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos p, Complex.sub_re, Real.rpow_add p, mul_left_comm]
    exact mul_le_mul_of_nonneg_left ((hb x).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg p.le _)))
      (Real.rpow_nonneg p.le _)
  refine ⟨fun z hz => ((hi _ hz.le).const_mul |C|).mono' (mz z) (.of_forall (nz z)), ?_⟩
  refine GroundTheory.Automorphic.PseudoEisenstein.differentiableOn_integral_of_bound
    (isOpen_lt continuous_const (by fun_prop)) (fun x z _ => ?_) (fun z _ => mz z) fun z hz => ?_
  · have : (A x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h0 x).ne'
    exact (DifferentiableAt.const_cpow (by fun_prop) (Or.inl this)).mul_const _ |>.differentiableWithinAt
  · have hz' : t₀ < z.re - s₀.re + q := hz
    set u := z.re - s₀.re + q with hu
    refine ⟨(u - t₀) / 2, by linarith, fun w hw => ?_, fun x => |C| * (A x ^ (u - (u - t₀) / 2) + A x ^ (u + (u - t₀) / 2)),
      (((hi _ (by linarith)).add (hi _ (by linarith))).const_mul _), fun w hw x => ?_⟩
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      show t₀ < w.re - s₀.re + q
      linarith [this.1]
    · have := (Complex.abs_re_le_norm (w - z)).trans (mem_closedBall_iff_norm.1 hw)
      rw [Complex.sub_re, abs_le] at this
      refine (nz w x).trans (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _))
      have p := h0 x
      have p1 := Real.rpow_pos_of_pos p (u - (u - t₀) / 2)
      have p2 := Real.rpow_pos_of_pos p (u + (u - t₀) / 2)
      rcases le_total 1 (A x) with h | h
      · have := Real.rpow_le_rpow_of_exponent_le h (show w.re - s₀.re + q ≤ u + (u - t₀) / 2 by linarith [this.2])
        linarith
      · have := Real.rpow_le_rpow_of_exponent_ge p h (show u - (u - t₀) / 2 ≤ w.re - s₀.re + q by linarith [this.1])
        linarith
private theorem coef_facts_pk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Γ : Subgroup G} [Countable Γ] {D : Set G}
    (hD : IsFundamentalDomain Γ D μ) [IsFiniteMeasure (μ.restrict D)] {φ : G → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ g, ‖φ g‖ ≤ C)
    (hi : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) :
    Continuous (fun g => pet μ D (fun y => φ (y * g)) φ) ∧ (∃ C' : ℝ, ∀ g, ‖pet μ D (fun y => φ (y * g)) φ‖ ≤ C') ∧
      ∀ g, pet μ D (fun y => φ (y * g⁻¹)) φ = star (pet μ D (fun y => φ (y * g)) φ) := by
  have C0 : 0 ≤ C := (norm_nonneg _).trans (hb 1)
  have nb : ∀ g y, ‖φ (y * g) * star (φ y)‖ ≤ C * C := fun g y => by
    rw [norm_mul, norm_star]; exact mul_le_mul (hb _) (hb _) (norm_nonneg _) C0
  have cm : ∀ g, Continuous fun y => φ (y * g) * star (φ y) := fun g => by fun_prop
  refine ⟨continuous_of_dominated (bound := fun _ => C * C) (fun g => (cm g).aestronglyMeasurable)
    (fun g => .of_forall (nb g)) (integrable_const _) (.of_forall fun y => by fun_prop), ⟨C * C * (μ.restrict D).real Set.univ, fun g => ?_⟩, fun g => ?_⟩
  · simpa [pet] using norm_integral_le_of_norm_le_const (μ := μ.restrict D) (.of_forall (nb g))
  · let f : G → ℂ := fun y => φ y * star (φ (y * g))
    have hf : ∀ (γ : Γ) x, f (γ • x) = f x := fun γ x => by
      simp only [f, Subgroup.smul_def, smul_eq_mul, mul_assoc]
      rw [hi _ γ.2, hi _ γ.2]
    have h2 : IsFundamentalDomain Γ (MulOpposite.op g⁻¹ • D) μ := hD.smul_of_comm (MulOpposite.op g⁻¹)
    have h3 : ∫ y in MulOpposite.op g⁻¹ • D, f y ∂μ = ∫ y in D, f (y * g⁻¹) ∂μ := by
      exact (measurePreserving_mul_right μ g⁻¹).setIntegral_image_emb (measurableEmbedding_mulRight g⁻¹) f D
    have h4 := h2.setIntegral_eq hD hf
    rw [h3] at h4
    simp only [pet]
    simp only [f, inv_mul_cancel_right] at h4
    rw [h4, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp [mul_comm]
theorem _root_.UpperTheory.TP.rallis_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Rallis_k := by
  intro T F E _ _ _ _ _ σ B n d X W M χX χW om hP hn hd K a e hK ha he t₀ hi hlt ν hν Φ hΦ φ hφ
  have h0 : min n 0 = 0 := by simp
  have h0' : min d 0 = 0 := by simp
  have cX := T.cpt F E σ B _ X _ _ hP.base (.inl hP.herm) h0
  have cW := T.cpt F E σ B _ W _ _ hP.base (.inr hP.skew) h0'
  obtain ⟨μ, D, hμ, hD⟩ := cW.ex
  have hKc := T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm) K hK
  have hJ := _root_.GlobalTheory.ThK.Dbl.aniso_of_k hP.base (.inl hP.herm) h0
  obtain ⟨⟨K₁, a₁, hK₁, ha₁, ca, a0⟩, e₁, ce, he₁⟩ := _root_.GlobalTheory.ThK.Dbl.hgtEx_of_k T.stab2 F E σ B _ X _ _ hP.base (.inl hP.herm)
  have eK : K₁ = K := Subgroup.ext fun k => (hK₁ k).trans (hK k).symm
  subst eK
  have ea : a₁ = a := funext fun x => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa x
    rw [ha.val p t hp k hk, ha₁.val p t hp k hk]
  subst ea
  have ee : e₁ = e := MonoidHom.ext fun x => Subtype.ext (Units.ext ((he₁ x.1 x.2).trans (he x.1 x.2).symm))
  subst ee
  haveI := cX.sc; haveI := cW.sc; haveI := cX.lc; haveI := cW.lc; haveI := cX.cnt; haveI := hP.good.haar; haveI := cX.right M.μ hP.good.haar
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by rw [Measure.restrict_apply_univ]; exact cW.fin _ _ hμ hD⟩
  haveI : IsFiniteMeasure (M.μ.restrict M.dom) := ⟨by rw [Measure.restrict_apply_univ]; exact cX.fin _ _ hP.good.haar hP.good.dom⟩
  obtain ⟨c, c1, hc1⟩ := inv_scale M.μ
  have s1 := T.polSch F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP Φ hΦ
  have bT := (T.basic F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP).1 Φ s1
  obtain ⟨dd, om₂, S, l, d1, d2, d3, d4⟩ := T.dbl F E σ B _ _ _ _ _ _ _ _ _ _ _ _ hP
  obtain ⟨c', c0, hc⟩ := d4 ν hν
  have c2 : (c' : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have sec := T.boxSec F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1 K₁ a₁ hK ha Φ hΦ Φ hΦ
  obtain ⟨U, Ê, hE, u, hv⟩ := T.swFull F E σ B _ _ _ _ M _ _ _ _ hP.base hn hd hP.herm hP.skew h0' hP.good χW hP.hW hP.resW dd om₂ S l d3 d1
    K₁ a₁ hK ha μ D hμ hD Φ hΦ Φ hΦ
  set f : G2 σ X → ℂ := fun x => l (om₂ x (boxFun Φ (star Φ))) with hf
  set s₀ : ℂ := ((d : ℂ) - n) / 2 with hs₀
  have hap : ∀ g, a₁ (e₁ (1, g)) = a₁ (e₁ (g⁻¹, 1)) := fun g => by
    have := ha.mul (he g g).par (e₁ (g⁻¹, 1))
    rw [absE_det hJ, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at this
    simpa using this
  have hi' : ∀ t, t₀ ≤ t → Integrable (fun g => a₁ (e₁ (1, g)) ^ t) M.μ := fun t ht => by
    have h1 : Integrable (fun g => (((a₁ (e₁ (1, g)) ^ t : ℝ) : ℂ))) M.μ := (hc1 _).1 (by
      simpa [hap] using (hi t ht).ofReal (𝕜 := ℂ))
    simpa using h1.re
  have idf : ∀ g, f (e₁ (1, g)) * detInv χW g = c' * coef om ν Φ g⁻¹ := fun g => by
    have h1 := Law.diag sec.law hJ he g (e₁ (g⁻¹, 1))
    rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one] at h1
    have e2 := ((d2 Φ s1 Φ s1).2 1 g⁻¹ 1 _ (he _ _)).2
    rw [detInv_rat hP.hW (one_mem _), one_smul, show ((1, 1) : UA σ X.J × UA σ W.J) = 1 from rfl, map_one, Module.End.one_apply] at e2
    rw [h1, hf]
    simp only [e2]
    rw [hc _ (hP.weil.isUSplitting.pres _ _ s1) _ s1, coef]
  have cF : Continuous (coef om ν Φ) := by
    have h1 : coef om ν Φ = fun g => (c' : ℂ)⁻¹ * (f (e₁ (1, g⁻¹)) * detInv χW g⁻¹) := funext fun g => by
      rw [idf, inv_inv, inv_mul_cancel_left₀ c2]
    rw [h1]
    exact continuous_const.mul ((sec.cont.comp (ce.comp (continuous_const.prodMk continuous_inv))).mul
      ((continuous_detInv hP.hW).comp continuous_inv))
  obtain ⟨Cf, hCf⟩ := Law.bound sec.law sec.cont ha hKc
  have hre : (s₀ + (n : ℂ) / 2).re = (d : ℝ) / 2 := by
    have : s₀ + (n : ℂ) / 2 = (((d : ℝ) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have bF : ∀ g, ‖coef om ν Φ g‖ ≤ (c'⁻¹ * Cf) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    have h1 := idf g⁻¹
    rw [inv_inv] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_detInv, mul_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg c0.le] at h2
    have h3 := hCf (e₁ (1, g⁻¹))
    rw [hre, hap, inv_inv, h2] at h3
    rw [mul_assoc, le_inv_mul_iff₀ c0]
    exact h3
  obtain ⟨Cφ, hCφ⟩ := cX.bdd hφ.1 hφ.2
  obtain ⟨cm, ⟨Cm, hCm⟩, im⟩ := coef_facts_pk hP.good.dom hφ.1 hCφ hφ.2
  change Continuous (mc M φ) at cm
  change ∀ g, ‖mc M φ g‖ ≤ Cm at hCm
  change ∀ g, mc M φ g⁻¹ = star (mc M φ g) at im
  have Cm0 : 0 ≤ Cm := (norm_nonneg _).trans (hCm 1)
  have a0' : ∀ g, 0 < a₁ (e₁ (g, 1)) := fun g => a0 _
  have mA : Measurable fun g => a₁ (e₁ (g, 1)) :=
    (ca.comp (ce.comp (continuous_id.prodMk continuous_const))).measurable
  have hb : ∀ g, ‖coef om ν Φ g * star (mc M φ g)‖ ≤ (c'⁻¹ * Cf * Cm) * a₁ (e₁ (g, 1)) ^ ((d : ℝ) / 2) := fun g => by
    rw [norm_mul, norm_star, mul_right_comm]
    exact mul_le_mul (bF g) (hCm g) (norm_nonneg _) ((norm_nonneg _).trans (bF g))
  obtain ⟨iZ, dZ⟩ := cpow_integral_pk a0' mA (cF.mul cm.star).aestronglyMeasurable hb hi s₀
  have hsr : s₀.re = ((d : ℝ) - n) / 2 := by
    have : s₀ = ((((d : ℝ) - n) / 2 : ℝ) : ℂ) := by rw [hs₀]; push_cast; ring
    rw [this, Complex.ofReal_re]
  have ib : Integrable (fun g => coef om ν Φ g * star (mc M φ g)) M.μ := by
    simpa using iZ s₀ (by simpa using hlt)
  refine ⟨ib, fun L0 => ?_⟩
  obtain ⟨hol, t₁, far⟩ := _root_.GlobalTheory.ThK.Dbl.kpair_cont_k hP.base (.inl hP.herm) h0 cX hP.hW he ce hKc ha ca a0 sec.cont sec.law hE hP.good.haar hP.good.dom hi'
  have rp : IsRapid φ := cX.rapid hφ.1 hφ.2
  have eqP : ∀ z : ℂ, t₁ < z.re → kpair χW e₁ M.μ M.dom (Ê z) φ =
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ) := fun z hz => by
    have ez : ∀ g, flat a₁ f s₀ z (e₁ (1, g)) * detInv χW g * pet M.μ M.dom (fun h => φ (h * g)) φ =
        c' * ((a₁ (e₁ (g⁻¹, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g⁻¹ * star (mc M φ g⁻¹))) := fun g => by
      have h1 : star (mc M φ g⁻¹) = pet M.μ M.dom (fun h => φ (h * g)) φ := by rw [im, star_star]; rfl
      rw [h1, flat, hap, mul_assoc (_ ^ _), idf]
      ring
    rw [(far z hz).2.2 φ rp]
    simp only [ez]
    rw [(hc1 fun g => c' * ((a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)))).2, integral_const_mul]
  have H0 := zero_of_half_pk (τ := t₀ + s₀.re - (d : ℝ) / 2) hE.isOpen hE.disc
    (f := fun z => kpair χW e₁ M.μ M.dom (Ê z) φ -
      c * (c' * ∫ g, (a₁ (e₁ (g, 1)) : ℂ) ^ (z - s₀) * (coef om ν Φ g * star (mc M φ g)) ∂M.μ))
    (((hol φ rp).mono Set.inter_subset_left).sub (((dZ.mono fun z hz => by
      have : t₀ + s₀.re - (d : ℝ) / 2 < z.re := hz.2
      show t₀ < z.re - s₀.re + (d : ℝ) / 2
      linarith).const_mul _).const_mul _))
    (t := t₁) (fun z hz => ⟨(far z hz).1, sub_eq_zero.2 (eqP z hz)⟩) u (by linarith)
  have cT : Continuous fun x : UA σ W.J × UA σ X.J => theta om Φ x.2 x.1 := bT.1.comp continuous_swap
  have key := An.at_value (φ := φ) (M.μ.restrict M.dom) (μ.restrict D)
    ⟨cT, cW.bdd₂ cX cT fun γ hγ δ hδ g g' => bT.2.1 δ hδ γ hγ _ _⟩ ⟨hφ.1, Cφ, hCφ⟩
  have zl : ∀ h, ∫ g in M.dom, φ g * star (theta om Φ g h) ∂M.μ = 0 := fun h => by
    have h1 : lift M om Φ φ h = 0 := congrFun L0 h
    have h2 : star (lift M om Φ φ h) = 0 := by rw [h1, star_zero]
    rw [← h2, lift, Complex.star_def, ← integral_conj]
    refine integral_congr_ae (.of_forall fun g => ?_)
    simp [mul_comm]
  simp only [zl, zero_mul, integral_zero] at key
  have hk : kpair χW e₁ M.μ M.dom (Ê s₀) φ = (if n < d then 1 else 2) * (((μ.real D)⁻¹ : ℝ) : ℂ) *
      ∫ y, (∫ h in D, theta om Φ y.1 h * star (theta om Φ y.2 h) ∂μ) * (φ y.2 * star (φ y.1)) ∂(M.μ.restrict M.dom).prod (M.μ.restrict M.dom) := by
    rw [kpair, ← integral_const_mul]
    refine integral_congr_ae (.of_forall fun y => ?_)
    simp only [hv, setAverage_eq, Complex.real_smul, ← fun g => (((d2 Φ s1 Φ s1).2 g y.1 y.2 _ (he _ _)).1), integral_const_mul]
    ring
  have H1 : c * (c' * ∫ g, coef om ν Φ g * star (mc M φ g) ∂M.μ) = 0 := by
    have h2 : kpair χW e₁ M.μ M.dom (Ê s₀) φ = 0 := by rw [hk, key, mul_zero]
    simpa [h2] using H0
  exact (mul_eq_zero.1 ((mul_eq_zero.1 H1).resolve_left c1)).resolve_left c2
end UpperTheory.TP
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
private theorem abs_tail_pk {G D C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [Group D] [TopologicalSpace D] [IsTopologicalGroup D] [MeasurableSpace D] [BorelSpace D]
    [LocallyCompactSpace D] [SecondCountableTopology D]
    [Group C] [TopologicalSpace C] [IsTopologicalGroup C] [MeasurableSpace C] [BorelSpace C]
    [LocallyCompactSpace C] [SecondCountableTopology C]
    (j : D × C ≃ₜ* G) (μ : Measure G) [μ.IsHaarMeasure] (μC : Measure C) [μC.IsHaarMeasure]
    {U W : Set G} {K : Set C} (hU : IsOpen U) (hUc : IsCompact U) (h1 : (1 : G) ∈ U)
    (hK : MeasurableSet K) (f : G → ENNReal) (F : C → ENNReal) (hF : Measurable F)
    (hc : ∀ d c, j (d, c) ∈ U → j (d, 1) ∈ U ∧ c ∈ K)
    (hm : ∀ d c, j (d, 1) ∈ U → c ∉ K → j (d, c) ∈ W ∧ f (j (d, c)) = F c)
    (hlt : ∫⁻ g in W, f g ∂μ < μ U) : ∫⁻ c in Kᶜ, F c ∂μC < μC K := by
  let μD : Measure D := Measure.haar
  let T : Set D := {d | j (d, 1) ∈ U}
  have cj : Continuous fun d : D => j (d, 1) := j.continuous.comp (by fun_prop)
  have oT : IsOpen T := hU.preimage cj
  have m1 : (1 : D) ∈ T := by
    show j ((1 : D), (1 : C)) ∈ U
    rw [show ((1 : D), (1 : C)) = 1 from rfl, map_one]; exact h1
  have t0 : μD T ≠ 0 := (oT.measure_pos μD ⟨1, m1⟩).ne'
  have tt : μD T ≠ ⊤ := by
    have cpt : IsCompact (Prod.fst '' (j.symm '' U)) := (hUc.image j.symm.continuous).image continuous_fst
    refine ((measure_mono ?_).trans_lt cpt.measure_lt_top).ne
    intro d hd
    exact ⟨(d, 1), ⟨j (d, 1), hd, j.symm_apply_apply _⟩, rfl⟩
  let P : Measure (D × C) := μD.prod μC
  have me : MeasurableEmbedding j := j.toHomeomorph.measurableEmbedding
  have hH : (P.map j).IsHaarMeasure := j.toMulEquiv.isHaarMeasure_map P j.continuous j.symm.continuous
  have hν : P.map j = Measure.haarScalarFactor (P.map j) μ • μ := Measure.isMulLeftInvariant_eq_smul (P.map j) μ
  have k0 : Measure.haarScalarFactor (P.map j) μ ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne'
  have a1 : μD T * ∫⁻ c in Kᶜ, F c ∂μC = ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P := by
    rw [← Measure.prod_restrict, lintegral_prod (fun y : D × C => F y.2) (hF.comp measurable_snd).aemeasurable]
    simp [lintegral_const, mul_comm]
  have a2 : ∫⁻ y in T ×ˢ Kᶜ, F y.2 ∂P ≤ ∫⁻ g in W, f g ∂(P.map j) := by
    rw [me.restrict_map, me.lintegral_map]
    calc _ = ∫⁻ y in T ×ˢ Kᶜ, f (j y) ∂P :=
          setLIntegral_congr_fun (oT.measurableSet.prod hK.compl) fun y hy => (hm y.1 y.2 hy.1 hy.2).2.symm
      _ ≤ _ := lintegral_mono_set fun y hy => (hm _ _ hy.1 hy.2).1
  have a3 : (P.map j) U ≤ μD T * μC K := by
    rw [me.map_apply, ← Measure.prod_prod]
    exact measure_mono fun y hy => hc y.1 y.2 hy
  have a4 : ∫⁻ g in W, f g ∂(P.map j) < (P.map j) U := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, Measure.smul_apply]
    have hk : ((Measure.haarScalarFactor (P.map j) μ : ℝ≥0) : ENNReal) ≠ 0 := by exact_mod_cast k0
    simp only [ENNReal.smul_def, smul_eq_mul]
    exact (ENNReal.mul_lt_mul_iff_right hk ENNReal.coe_ne_top).2 hlt
  have := (a1.le.trans a2).trans_lt (a4.trans_le a3)
  exact (ENNReal.mul_lt_mul_iff_right t0 tt).1 this
section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {X : Spc F E n} {v : Pl F}
private theorem fix_off_pk {g : UA σ X.J} (hg : OffAt v g) {z : Fin n → AE F E} (hz : At (evFin F v) z) : mat g *ᵥ z = z := by
  have h : PositivityTheory.ThKG.Loc.idem F v • (mat g - 1) = 0 := Matrix.ext fun i j => Bad.idem_off (by
    have := congrFun₂ hg i j
    rw [Matrix.map_apply] at this
    simp [this, Matrix.one_apply, apply_ite (compFin F E v)])
  have e : (mat g - 1) *ᵥ z = 0 := by
    rw [← Bad.idem_smul hz, Matrix.mulVec_smul, ← Matrix.smul_mulVec, h, Matrix.zero_mulVec]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at e
  exact e
private theorem int_of_off_pk {g : UA σ X.J} (hg : OffAt v g) : IntAt v g := fun z hz h => by
  have e := fix_off_pk hg h
  have e' : mat g⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← e]
    rw [Matrix.mulVec_mulVec, ← Euler.mm, inv_mul_cancel]
    exact Matrix.one_mulVec z
  exact ⟨e.symm ▸ hz, e'.symm ▸ hz⟩
private theorem int_gOff_pk {S : Finset (Pl F)} {c : UA σ X.J} (hc : c ∈ gOff σ X S) (hv : v ∈ S) : IntAt v c :=
  (Subgroup.closure_le (Euler.intGrp σ X v)).2 (fun _ hg => int_of_off_pk (hg.2 v hv)) hc
private theorem int_gAt_pk {S : Finset (Pl F)} {b : UA σ X.J} (hb : b ∈ gAt σ X S) (hv : v ∉ S) : IntAt v b := by
  have : gAt σ X S ≤ Euler.intGrp σ X v := iSup₂_le fun w hw x hx => by
    have hvw : v ≠ w := fun e => hv (e ▸ hw)
    have := (Euler.int_mul_ne hvw hx 1).2 (Euler.intGrp σ X v).one_mem
    rwa [mul_one] at this
  exact this hb
private theorem hgt_right_pk {K : Subgroup (G2 σ X)} {a : G2 σ X → ℝ} (ha : IsHgt K a) (x : G2 σ X) {k : G2 σ X} (hk : k ∈ K) :
    a (x * k) = a x := by
  obtain ⟨p, t, hp, k', hk', rfl⟩ := ha.iwa x
  rw [mul_assoc, ha.val p t hp _ (K.mul_mem hk' hk), ha.val p t hp k' hk']
end
end UpperTheory.TP
open UpperTheory.TP in
theorem UpperTheory.TP.tail_k :
    _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.Tail_k := by
  intro T F E _ _ _ _ _ σ B n X hB hX K a e hK ha he μ t hμ hi S₀
  classical
  have := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨a1, a2, a3⟩ := Euler.lcsc_UA σ X.J
  have hL := hX.lat
  have dec := _root_.UpperTheory.TP.decomp_k T F E σ B n X hB hX
  let U : Set (UA σ X.J) := {g | IntAll g}
  have Um : ∀ {x y : UA σ X.J}, IntAll x → IntAll y → IntAll (x * y) := fun hx hy v => (Euler.intGrp σ X v).mul_mem (hx v) (hy v)
  have Ui : ∀ {x : UA σ X.J}, IntAll x → IntAll x⁻¹ := fun hx v => (Euler.intGrp σ X v).inv_mem (hx v)
  have U1 : IntAll (1 : UA σ X.J) := fun v => (Euler.intGrp σ X v).one_mem
  obtain ⟨-, -, -, -, cU, oU, -, -, -⟩ := dec ∅
  have hr : ∀ g u : UA σ X.J, IntAll u → a (e (g * u, 1)) = a (e (g, 1)) := fun g u hu => by
    have : e (g * u, 1) = e (g, 1) * e (u, 1) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
    rw [this, hgt_right_pk ha _ (_root_.GlobalTheory.ThK.Dbl.Bad.emb_mem_k hB hX (by simp) hK he hu)]
  have lc : IsLocallyConstant fun g : UA σ X.J => a (e (g, 1)) := (IsLocallyConstant.iff_exists_open _).2 fun g =>
    ⟨{x | g⁻¹ * x ∈ U}, oU.preimage (by fun_prop), by show g⁻¹ * g ∈ U; rw [inv_mul_cancel]; exact U1, fun x hx => by
      have := hr g _ hx
      rwa [mul_inv_cancel_left] at this⟩
  let f : UA σ X.J → ENNReal := fun g => ENNReal.ofReal (a (e (g, 1)) ^ t)
  have cf : Continuous f := (lc.comp fun r => ENNReal.ofReal (r ^ t)).continuous
  let m : Measure (UA σ X.J) := μ.withDensity f
  have mfin : m Set.univ ≠ ⊤ := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact hi.lintegral_lt_top.ne
  let A : Finset (Pl F) → Set (UA σ X.J) := fun S => {g | ∀ v ∈ S, IntAt v g} \ U
  have mA : ∀ S, MeasurableSet (A S) := fun S => by
    refine MeasurableSet.diff ?_ oU.measurableSet
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => Euler.isClosed_int hL u).measurableSet
  have anti : Antitone A := fun S S' hS g hg => ⟨fun v hv => hg.1 v (hS hv), hg.2⟩
  have emp : ⋂ S, A S = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun g hg => ?_
    have hg' := Set.mem_iInter.1 hg
    exact (hg' ∅).2 fun v => (hg' {v}).1 v (Finset.mem_singleton_self v)
  have ten := tendsto_measure_iInter_atTop (μ := m) (fun S => (mA S).nullMeasurableSet) anti
    ⟨∅, ne_top_of_le_ne_top mfin (measure_mono (Set.subset_univ _))⟩
  rw [emp, measure_empty] at ten
  have pos : 0 < μ U := oU.measure_pos μ ⟨1, U1⟩
  obtain ⟨S, hlt, hS⟩ := ((ten.eventually (gt_mem_nhds pos)).and (eventually_ge_atTop S₀)).exists
  refine ⟨S, hS, fun μC hC => ?_⟩
  obtain ⟨⟨j, hj⟩, cI, cA, cO, -, -, iI, -, -⟩ := dec S
  have : LocallyCompactSpace (gInf σ X) := cI.isClosed.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gAt σ X S) := cA.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : LocallyCompactSpace (gOff σ X S) := cO.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology (gInf σ X) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gAt σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology (gOff σ X S) := IsEmbedding.subtypeVal.secondCountableTopology
  let j' : (gInf σ X × gAt σ X S) × gOff σ X S ≃ₜ* UA σ X.J :=
    { toMulEquiv := MulEquiv.prodAssoc.trans j.toMulEquiv
      continuous_toFun := j.continuous.comp ((continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      continuous_invFun := by
        have := j.symm.continuous
        exact ((continuous_fst.prodMk (continuous_fst.comp continuous_snd)).prodMk (continuous_snd.comp continuous_snd)).comp this }
  have hj' : ∀ d c, j' (d, c) = d.1.1 * d.2.1 * c.1 := fun d c => hj (d.1, d.2, c)
  have hj1 : ∀ d, j' (d, 1) = d.1.1 * d.2.1 := fun d => by rw [hj']; simp
  have hcm : ∀ d c, j' (d, c) = c.1 * (d.1.1 * d.2.1) := fun d c => by
    have := map_mul j' ((1 : gInf σ X × gAt σ X S), c) (d, (1 : gOff σ X S))
    rw [Prod.mk_mul_mk, one_mul, mul_one, hj1] at this
    rw [this, hj']
    simp
  have res := abs_tail_pk j' μ μC (U := U) (W := A S) (K := {c | IntAll c.1}) oU cU U1
    (oU.preimage continuous_subtype_val).measurableSet f (fun c => f c.1) (cf.measurable.comp measurable_subtype_coe)
    (fun d c hg => by
      have hx : IntAll d.1.1 := iI _ d.1.2
      have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
      have hb : IntAll d.2.1 := fun v => by
        by_cases hv : v ∈ S
        · have e1 : d.2.1 = d.1.1⁻¹ * (d.1.1 * d.2.1 * c.1) * c.1⁻¹ := by group
          rw [e1]
          exact (Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).mul_mem ((Euler.intGrp σ X v).inv_mem (hx v)) (hg' v))
            ((Euler.intGrp σ X v).inv_mem (int_gOff_pk c.2 hv))
        · exact int_gAt_pk d.2.2 hv
      have hxb := Um hx hb
      refine ⟨by rw [hj1]; exact hxb, ?_⟩
      show IntAll c.1
      have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
      rw [e2]
      exact Um (Ui hxb) hg')
    (fun d c hd hcK => by
      have hd' : IntAll (d.1.1 * d.2.1) := hj1 d ▸ hd
      refine ⟨⟨fun v hv => ?_, fun hg => hcK ?_⟩, ?_⟩
      · rw [hj']
        exact (Euler.intGrp σ X v).mul_mem (hd' v) (int_gOff_pk c.2 hv)
      · have hg' : IntAll (d.1.1 * d.2.1 * c.1) := hj' d c ▸ hg
        show IntAll c.1
        have e2 : c.1 = (d.1.1 * d.2.1)⁻¹ * (d.1.1 * d.2.1 * c.1) := by group
        rw [e2]
        exact Um (Ui hd') hg'
      · show ENNReal.ofReal (a (e (j' (d, c), 1)) ^ t) = ENNReal.ofReal (a (e (c.1, 1)) ^ t)
        rw [hcm, hr _ _ hd'])
    (by
      rw [← withDensity_apply _ (mA S)]
      exact hlt)
  exact res
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
namespace UpperTheory.TP
private theorem assemble_pk {H A V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
    (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsOpenPosMeasure] (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) (Ω : Set H) (hΩ : IsCompact Ω) (hcov : ∀ g, ∃ γ ∈ Γ, γ * g ∈ Ω)
    [Group A] [MeasurableSpace A] [MeasurableMul A] (μA : Measure A) [IsFiniteMeasure μA] [μA.IsMulLeftInvariant]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V] (π : A →* Module.End ℂ V)
    (hI : ∀ W : Submodule ℂ V, (∀ g, ∀ w ∈ W, π g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ι : A →* H) (hι : Measurable ι)
    (f : V →ₗ[ℂ] (H → ℂ)) (hf0 : ∀ a, f a = 0 → a = 0) (hfc : ∀ a, Continuous (f a))
    (hfl : ∀ a, ∀ γ ∈ Γ, ∀ h, f a (γ * h) = f a h) (hfr : ∀ x a y, f (π x a) y = f a (y * ι x))
    (B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (hB₁ : ∀ g a b, B₁ (π g a) (π g b) = B₁ a b) (x₀ : V)
    (u : H → ℂ) (huc : Continuous u) (hul : ∀ γ ∈ Γ, ∀ h, u (γ * h) = u h) :
    ∫ x, B₁ (π x x₀) x₀ * star (pet μ 𝓕 (fun y => u (y * ι x)) (f x₀)) ∂μA =
      ((μA.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ) * B₁ x₀ x₀ * star (pet μ 𝓕 u (f x₀)) := by
  have P := fun g₁ g₂ c₁ c₂ l₁ l₂ => UpperTheory.innerProduct_integral_fundamentalDomain_of_compact μ Γ 𝓕 h𝓕 hfin Ω hΩ hcov g₁ g₂ c₁ c₂ l₁ l₂
  have hpet : ∀ g₁ g₂ : H → ℂ, pet μ 𝓕 g₁ g₂ = ∫ h in 𝓕, g₁ h * starRingEnd ℂ (g₂ h) ∂μ := fun _ _ => rfl
  have addL : ∀ g₁ g₂ g₃ : H → ℂ, Continuous g₁ → Continuous g₂ → Continuous g₃ → (∀ γ ∈ Γ, ∀ h, g₁ (γ * h) = g₁ h) →
      (∀ γ ∈ Γ, ∀ h, g₂ (γ * h) = g₂ h) → (∀ γ ∈ Γ, ∀ h, g₃ (γ * h) = g₃ h) →
      pet μ 𝓕 (g₁ + g₂) g₃ = pet μ 𝓕 g₁ g₃ + pet μ 𝓕 g₂ g₃ := fun g₁ g₂ g₃ c₁ c₂ c₃ l₁ l₂ l₃ => by
    simp only [hpet, Pi.add_apply, add_mul]
    exact integral_add (P _ _ c₁ c₃ l₁ l₃).1 (P _ _ c₂ c₃ l₂ l₃).1
  have addR : ∀ g₁ g₂ g₃ : H → ℂ, Continuous g₁ → Continuous g₂ → Continuous g₃ → (∀ γ ∈ Γ, ∀ h, g₁ (γ * h) = g₁ h) →
      (∀ γ ∈ Γ, ∀ h, g₂ (γ * h) = g₂ h) → (∀ γ ∈ Γ, ∀ h, g₃ (γ * h) = g₃ h) →
      pet μ 𝓕 g₃ (g₁ + g₂) = pet μ 𝓕 g₃ g₁ + pet μ 𝓕 g₃ g₂ := fun g₁ g₂ g₃ c₁ c₂ c₃ l₁ l₂ l₃ => by
    simp only [hpet, Pi.add_apply, map_add, mul_add]
    exact integral_add (P _ _ c₃ c₁ l₃ l₁).1 (P _ _ c₃ c₂ l₃ l₂).1
  have smL : ∀ (c : ℂ) (g₁ g₂ : H → ℂ), pet μ 𝓕 (c • g₁) g₂ = c * pet μ 𝓕 g₁ g₂ := fun c g₁ g₂ => by
    simp only [hpet, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul _ _
  have smR : ∀ (c : ℂ) (g₁ g₂ : H → ℂ), pet μ 𝓕 g₁ (c • g₂) = starRingEnd ℂ c * pet μ 𝓕 g₁ g₂ := fun c g₁ g₂ => by
    simp only [hpet, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c)]
    exact integral_const_mul _ _
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun a b => pet μ 𝓕 (f a) (f b))
    (fun a b c => by
      rw [map_add]; exact addL _ _ _ (hfc a) (hfc b) (hfc c) (hfl a) (hfl b) (hfl c))
    (fun c a b => by rw [map_smul]; exact smL _ _ _)
    (fun a b c => by
      rw [map_add]; exact addR _ _ _ (hfc b) (hfc c) (hfc a) (hfl b) (hfl c) (hfl a))
    (fun c a b => by rw [map_smul]; exact smR _ _ _)
  have hB : ∀ a b, B a b = pet μ 𝓕 (f a) (f b) := fun _ _ => rfl
  have hh : ∀ a b, B b a = star (B a b) := fun a b => by
    simp only [hB, hpet]
    rw [show star (∫ h in 𝓕, f a h * starRingEnd ℂ (f b h) ∂μ) = starRingEnd ℂ (∫ h in 𝓕, f a h * starRingEnd ℂ (f b h) ∂μ) from rfl,
      ← integral_conj]
    congr 1
    funext h
    simp [mul_comm]
  have hp : ∀ a, a ≠ 0 → 0 < (B a a).re := fun a ha =>
    (P _ _ (hfc a) (hfc a) (hfl a) (hfl a)).2.2 fun h => ha (hf0 a h)
  have hinv : ∀ g a b, B (π g a) (π g b) = B a b := fun g a b => by
    simp only [hB, hpet, hfr]
    exact (P _ _ (hfc a) (hfc b) (hfl a) (hfl b)).2.1 (ι g)
  obtain ⟨c', hc'⟩ := UpperTheory.invariant_sesquilinearForm_eq_smul_of_irreducible π hI B hh hp hinv B₁ hB₁
  let L : V →ₗ⋆[ℂ] ℂ :=
    { toFun := fun b => pet μ 𝓕 u (f b)
      map_add' := fun a b => by rw [map_add]; exact addR _ _ _ (hfc a) (hfc b) huc (hfl a) (hfl b) hul
      map_smul' := fun c a => by rw [map_smul]; exact smR _ _ _ }
  obtain ⟨u₀, hu₀⟩ := UpperTheory.riesz_representation_sesquilinear B hh hp L
  have hL : ∀ b, pet μ 𝓕 u (f b) = B u₀ b := hu₀
  have key : ∀ x, pet μ 𝓕 (fun y => u (y * ι x)) (f x₀) = B (π x u₀) x₀ := fun x => by
    have e1 := (P (fun y => u (y * ι x)) (f x₀) (huc.comp (continuous_mul_right _)) (hfc x₀)
      (fun γ hγ h => by simp only [mul_assoc, hul γ hγ]) (hfl x₀)).2.1 (ι x⁻¹)
    have e2 : ∀ h, f x₀ (h * ι x⁻¹) = f (π x⁻¹ x₀) h := fun h => (hfr _ _ _).symm
    have e3 : ∀ h, u (h * ι x⁻¹ * ι x) = u h := fun h => by
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
    simp only [e2, e3] at e1
    rw [hpet, ← e1, ← hpet, hL, ← hinv x u₀]
    congr 1
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hm : ∀ a b, Measurable fun g => B (π g a) b := fun a b => by
    let l : H → V →ₗ[ℂ] ℂ := fun y => (LinearMap.proj y).comp f
    let Lb : V →ₗ[ℂ] ℂ :=
      { toFun := fun a => B a b
        map_add' := fun a a' => by simp
        map_smul' := fun c a => by simp }
    refine UpperTheory.measurable_of_separating_functionals l (fun a h => hf0 a (funext h)) (fun g => π g a) (fun y => ?_) Lb
    show Measurable fun g => f (π g a) y
    simp only [hfr]
    exact (hfc a).measurable.comp (measurable_const_mul y |>.comp hι)
  have hO := UpperTheory.irreducible_hermitian_form_unique μA π hI B hh hp hinv hm x₀ x₀ u₀ x₀
  simp only [key, hc']
  simp only [mul_assoc]
  rw [integral_const_mul]
  simp only [← mul_assoc] at hO ⊢
  rw [hO, hL x₀, hh x₀ u₀, star_star]
  have : star (B x₀ x₀) = B x₀ x₀ := (hh x₀ x₀).symm
  rw [this]
  ring
end UpperTheory.TP
theorem UpperTheory.TP.schurStep_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.SchurStep_k := by
  intro T E _ _ _ B n d X W M χX χW om P hn e e' he he' U hU f₀ hf₀ φ hφ hS ν hν φf hfin μA hμA
  obtain ⟨V, _, _, _, ρ, i, j, x₀, hirr, hi, hj, hjU, hA, hR⟩ := hS
  have C := T.cpt _ E (UpperTheory.TP.cj E) B n X n 0 P.base (Or.inl P.herm) (by simp)
  have D := _root_.UpperTheory.TP.decomp_k T _ E (UpperTheory.TP.cj E) B n X P.base P.herm ∅
  haveI := C.lc
  haveI := C.sc
  haveI := C.t2
  haveI := C.cnt
  haveI : BorelSpace (UA (UpperTheory.TP.cj E) X.J) := ⟨rfl⟩
  haveI hHaar : M.μ.IsHaarMeasure := P.good.haar
  haveI := C.right _ hHaar
  haveI : CompactSpace (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X) := isCompact_iff_compactSpace.1 D.2.1
  haveI : IsFiniteMeasure μA := inferInstance
  have hx₀ : x₀ ≠ 0 := fun h => hφ (by rw [← hj, h, map_zero])
  haveI : Nontrivial V := ⟨x₀, 0, hx₀⟩
  have hsymm : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, e.symm x.1 ∈ GlobalTheory.UnitaryBC.infU E n :=
    fun x => (he.inf _).1 (by simpa using x.2)
  let p : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X →* GlobalTheory.UnitaryBC.infU E n :=
    { toFun := fun x => ⟨e.symm x.1, hsymm x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp) }
  have hpe : ∀ x, e (p x).1 = x.1 := fun x => e.apply_symm_apply _
  have hpsurj : ∀ k : GlobalTheory.UnitaryBC.infU E n, ∃ x, p x = k := fun k =>
    ⟨⟨e k.1, (he.inf _).2 k.2⟩, Subtype.ext (e.symm_apply_apply _)⟩
  let π : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X →* Module.End ℂ V := ρ.comp p
  have hI : ∀ W' : Submodule ℂ V, (∀ g, ∀ w ∈ W', π g w ∈ W') → W' = ⊥ ∨ W' = ⊤ := fun W' h => by
    let S : Subrepresentation ρ := ⟨W', fun k v hv => by
      obtain ⟨x, rfl⟩ := hpsurj k
      exact h x v hv⟩
    rcases hirr.eq_bot_or_eq_top S with h1 | h1
    · exact Or.inl (congrArg Subrepresentation.toSubmodule h1)
    · exact Or.inr (congrArg Subrepresentation.toSubmodule h1)
  have hj0 : ∀ a, j a = 0 → a = 0 := fun a ha => by
    have hk := hI (LinearMap.ker j) (fun g w hw => by
      have hw' : j w = 0 := hw
      show j (ρ (p g) w) = 0
      rw [hR, hw', map_zero])
    rcases hk with h1 | h1
    · have : a ∈ LinearMap.ker j := ha
      rwa [h1, Submodule.mem_bot] at this
    · have : x₀ ∈ LinearMap.ker j := by rw [h1]; trivial
      exact absurd ((LinearMap.mem_ker.1 this).symm.trans (by rw [hj]) |>.symm) hφ
  let f : V →ₗ[ℂ] (UA (UpperTheory.TP.cj E) X.J → ℂ) := (LinearMap.funLeft ℂ ℂ e.symm).comp j
  have hfa : ∀ a y, f a y = j a (e.symm y) := fun _ _ => rfl
  have hf0 : ∀ a, f a = 0 → a = 0 := fun a ha => hj0 a (funext fun y => by
    have := congrFun ha (e y)
    rwa [hfa, e.symm_apply_apply] at this)
  have hleft : ∀ a, ∀ γ ∈ ratU (UpperTheory.TP.cj E) X.J, ∀ h, j a (e.symm (γ * h)) = j a (e.symm h) := fun a γ hγ h => by
    rw [map_mul]
    exact (hU.aut _ (hjU a)).left _ ((he.rat _).1 (by simpa using hγ)) _
  have hfc : ∀ a, Continuous (f a) := fun a => (hU.aut _ (hjU a)).cont.comp e.symm.continuous
  have hfr : ∀ x a y, f (π x a) y = f a (y * (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype x) := fun x a y => by
    show j (ρ (p x) a) (e.symm y) = j a (e.symm (y * x.1))
    rw [hR, map_mul]
    rfl
  have h2 : ∀ᶠ v in cofinite, φf v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers _ v} 1 :=
    (hfin.2.and P.good.std).mono fun v h => h.1.trans h.2
  have hrest := fun s => PositivityTheory.ThKG.Loc.Bump.rest_pure s φf hfin.1 h2
  let Ψ : V →ₗ[ℂ] ((Fin n × Fin d → AF (maximalRealSubfield E)) → ℂ) :=
    { toFun := fun a => pure (i a) φf
      map_add' := fun a b => by
        funext x
        simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
      map_smul' := fun c a => by
        funext x
        simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc] }
  have hΨa : ∀ a, Ψ a = pure (i a) φf := fun _ => rfl
  have hΨ : ∀ a, Ψ a ∈ schA _ (Fin n × Fin d) := fun a => (hrest (i a)).2
  have hact : ∀ x a, om (x.1, 1) (Ψ a) = Ψ (π x a) := fun x a => by
    have h := hA (p x) a _ (hrest (i a))
    rw [hpe] at h
    exact h
  have hsp := IsUWeilPair.isUSplitting P.weil
  let B₁ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => lD _ (Fin n × Fin d) (boxFun (Ψ a) (star (Ψ b))))
    (fun a b c => by rw [map_add, GlobalTheory.SchwartzBox.boxFun_add_left, map_add])
    (fun c a b => by rw [map_smul, GlobalTheory.SchwartzBox.boxFun_smul_left, map_smul]; rfl)
    (fun a b c => by rw [map_add, star_add, GlobalTheory.SchwartzBox.boxFun_add_right, map_add])
    (fun c a b => by rw [map_smul, star_smul, GlobalTheory.SchwartzBox.boxFun_smul_right, map_smul]; rfl)
  have hB₁a : ∀ a b, B₁ a b = lD _ (Fin n × Fin d) (boxFun (Ψ a) (star (Ψ b))) := fun _ _ => rfl
  have hB₁ : ∀ g a b, B₁ (π g a) (π g b) = B₁ a b := fun g a b => by
    rw [hB₁a, hB₁a, ← hact, ← hact]
    exact lD_unit hsp.unit hsp.pres (g.1, 1) (hΨ a) (hΨ b)
  obtain ⟨c, c0, hc⟩ := lD_haar ν hν
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 c0.ne'
  have hΦ : pure f₀ φf = Ψ x₀ := by rw [hΨa, hi]
  have hco : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, coef om ν (pure f₀ φf) x.1 = (c : ℂ)⁻¹ * B₁ (π x x₀) x₀ := fun x => by
    rw [hB₁a, hc _ (hΨ _) _ (hΨ _), inv_mul_cancel_left₀ hc0, ← hact, hΦ]
    rfl
  have hco1 : coef om ν (pure f₀ φf) 1 = (c : ℂ)⁻¹ * B₁ x₀ x₀ := by
    have := hco 1
    rwa [map_one, Module.End.one_apply] at this
  have hφU : φ ∈ U := hj ▸ hjU x₀
  have hform := hU.aut φ hφU
  obtain ⟨Ω, hΩ, hcov⟩ := C.cov
  refine ⟨((μA.real Set.univ / (Module.finrank ℂ V : ℝ) : ℝ) : ℂ), ?_, fun cc _ => ?_⟩
  · have h1 : 0 < μA.real Set.univ :=
      ENNReal.toReal_pos (IsOpen.measure_pos μA isOpen_univ Set.univ_nonempty).ne' (measure_ne_top _ _)
    have h3 : (0 : ℝ) < Module.finrank ℂ V := by exact_mod_cast Module.finrank_pos
    exact Complex.ofReal_ne_zero.2 (div_pos h1 h3).ne'
  have hmain := UpperTheory.TP.assemble_pk M.μ (ratU (UpperTheory.TP.cj E) X.J) M.dom P.good.dom (C.fin _ _ hHaar P.good.dom) Ω hΩ hcov μA π hI
    (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype measurable_subtype_coe f hf0 hfc hleft hfr B₁ hB₁ x₀
    (fun y => φ (e.symm (y * cc))) (hform.cont.comp (e.symm.continuous.comp (continuous_mul_right cc)))
    (fun γ hγ h => by
      show φ (e.symm (γ * h * cc)) = φ (e.symm (h * cc))
      rw [mul_assoc, map_mul]
      exact hform.left _ ((he.rat _).1 (by simpa using hγ)) _)
  have hfx : f x₀ = φ ∘ e.symm := funext fun y => by rw [hfa, hj]; rfl
  rw [hfx] at hmain
  have e1 : ∀ x : UpperTheory.TP.gInf (UpperTheory.TP.cj E) X, coef om ν (pure f₀ φf) x.1 * star (UpperTheory.TP.mc M (φ ∘ e.symm) (x.1 * cc)) =
      (c : ℂ)⁻¹ * (B₁ (π x x₀) x₀ * star (pet M.μ M.dom (fun y => φ (e.symm (y * (UpperTheory.TP.gInf (UpperTheory.TP.cj E) X).subtype x * cc))) (φ ∘ e.symm))) := fun x => by
    rw [hco, mul_assoc]
    simp only [UpperTheory.TP.mc, Function.comp_apply, mul_assoc, Subgroup.subtype_apply]
  simp_rw [e1]
  rw [integral_const_mul, hmain, hco1]
  have e2 : UpperTheory.TP.mc M (φ ∘ e.symm) cc = pet M.μ M.dom (fun y => φ (e.symm (y * cc))) (φ ∘ e.symm) := rfl
  rw [e2]
  ring
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.PRep Formalism.BasicNotions
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TP
open scoped Classical
section Gen
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
private theorem pure_mem_pol_pk {B : Base F E} {M : Model σ X W} {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb)
    {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (h : IsFin M φ) : pure f φ ∈ PolData B M :=
  Submodule.subset_span ⟨f, hf, φ, h.1, h.2, rfl⟩
private theorem pure_add'_pk {κ : Type} [Fintype κ] (f g : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (f + g) φ = pure f φ + pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
private theorem pure_smul'_pk {κ : Type} [Fintype κ] (a : ℂ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure (a • f) φ = a • pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
private theorem isFin_update_pk {M : Model σ X W} {φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ} (h : IsFin M φ) (v : Pl F)
    {ψ : (Fin n × Fin d → Fv F v) → ℂ} (hψ : ψ ∈ SB (Fin n × Fin d → Fv F v)) : IsFin M (Function.update φ v ψ) := by
  refine ⟨fun u => ?_, ?_⟩
  · by_cases hu : u = v
    · subst hu
      simpa using hψ
    · simpa [Function.update_of_ne hu] using h.1 u
  · filter_upwards [h.2, Filter.eventually_cofinite_ne v] with u hu hne
    rw [Function.update_of_ne hne]
    exact hu
end Gen
private theorem irr_pull_pk {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (q : H →* G) (hq : Function.Surjective q) (h : ρ.IsIrreducible) : Representation.IsIrreducible (ρ.comp q : Representation ℂ H V) := by
  rw [GlobalTheory.CuspRep.isIrreducible_iff] at h ⊢
  refine ⟨h.1, fun U hU => h.2 U fun g v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hq g
  exact hU x v hv
section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private theorem isSplit_prime_pk (hc : IsCMExt (maximalRealSubfield E) E (cj E)) {v : Pl (maximalRealSubfield E)}
    (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) : GlobalTheory.UnitaryBC.IsSplitAt (splitPrime t) :=
  ⟨splitPrime (t.comp (cj E)), splitPrime_comp_ne hc t, by rw [splitPrime_under, splitPrime_under]⟩
private theorem cLoc_surj_pk (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) :
    Function.Surjective ((GlobalTheory.UnitaryBC.cLoc (n := a) w).comp (GlobalTheory.UnitaryBC.locU a w).subtype) := fun g => by
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E a w hw
  exact ⟨e.symm g, by rw [MonoidHom.comp_apply, Subgroup.coe_subtype, ← he, e.apply_symm_apply]⟩
private theorem decomp_loc_pk (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) (g : GlobalTheory.UnitaryBC.UA E a) :
    ∃ h ∈ GlobalTheory.UnitaryBC.locU a w, ∀ h' ∈ GlobalTheory.UnitaryBC.locU a w, Commute (h⁻¹ * g) h' := by
  obtain ⟨x, hx, y, rfl, hy⟩ := GlobalTheory.Cong.exists_locU_mul_comm a w hw g
  exact ⟨x, hx, fun z hz => by rw [inv_mul_cancel_left]; exact hy z hz⟩
private theorem read_pair_pk {n d : ℕ} (w : HeightOneSpectrum (𝓞 E)) (hw : GlobalTheory.UnitaryBC.IsSplitAt w) (hA : AbsIso)
    {U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)} {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hU : GlobalTheory.UnitaryBC.IsAutRepU U) (hU' : GlobalTheory.UnitaryBC.IsAutRepU U')
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) (w.adicCompletion E))) (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) (w.adicCompletion E)))
    (hτ : CompAt U w τ) (hτ' : CompAt U' w τ')
    (P : (GlobalTheory.UnitaryBC.UA E n → ℂ) →+ (GlobalTheory.UnitaryBC.UA E d → ℂ)) (hPU : ∀ φ ∈ U, P φ ∈ U')
    {φ : GlobalTheory.UnitaryBC.UA E n → ℂ} (hφ : φ ∈ U) (hne : P φ ≠ 0) :
    ∃ (c : τ.V →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ)) (p : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] τ'.V) (x : τ.V),
      (∀ y, c y ∈ U) ∧
      (∀ (h : GlobalTheory.UnitaryBC.locU n w) y, c (τ.ρ (GlobalTheory.UnitaryBC.cLoc w h.1) y) = GlobalTheory.UnitaryBC.RU E n h.1 (c y)) ∧
      (∀ (h : GlobalTheory.UnitaryBC.locU d w), ∀ y ∈ U',
        p (GlobalTheory.UnitaryBC.RU E d h.1 y) = τ'.ρ (GlobalTheory.UnitaryBC.cLoc w h.1) (p y)) ∧
      p (P (c x)) ≠ 0 := by
  obtain ⟨hirr, f, hf0, hfU, hfe⟩ := hτ
  obtain ⟨hirr', f', hf0', hfU', hfe'⟩ := hτ'
  obtain ⟨⟨m, c, x, hcU, hce, hsum⟩, -⟩ := hA (GlobalTheory.UnitaryBC.UA E n) (GlobalTheory.UnitaryBC.UA E n → ℂ) τ.V (GlobalTheory.UnitaryBC.RU E n) U
    (GlobalTheory.UnitaryBC.locU n w) (τ.ρ.comp ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU n w).subtype))
    (decomp_loc_pk n w hw) hU.stable hU.irred (irr_pull_pk _ _ (cLoc_surj_pk n w hw) hirr) f hf0 hfU hfe φ hφ
  obtain ⟨p, hp0, hpe⟩ := (hA (GlobalTheory.UnitaryBC.UA E d) (GlobalTheory.UnitaryBC.UA E d → ℂ) τ'.V (GlobalTheory.UnitaryBC.RU E d) U'
    (GlobalTheory.UnitaryBC.locU d w) (τ'.ρ.comp ((GlobalTheory.UnitaryBC.cLoc w).comp (GlobalTheory.UnitaryBC.locU d w).subtype))
    (decomp_loc_pk d w hw) hU'.stable hU'.irred (irr_pull_pk _ _ (cLoc_surj_pk d w hw) hirr') f' hf0' hfU' hfe' (P φ) (hPU φ hφ)).2 hne
  have hs : ∑ i, p (P (c i (x i))) ≠ 0 := by
    rw [← map_sum, ← map_sum, ← hsum]
    exact hp0
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  exact ⟨c i, p, x i, hcU i, fun h y => hce i h y, fun h y hy => hpe h y hy, hi⟩
end CM
section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
theorem std_of_fin_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) {φ : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (h : IsFin M φ) : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers (maximalRealSubfield E)} 1 := by
  filter_upwards [h.2, hP.good.std] with v a b using a.trans b
theorem real_part_k (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0)
    (Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ))
    (hΘ : ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
      ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
        Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ))
    {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)} {pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hp : ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f))
    {f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)} (hf₀ : f₀ ∈ M.Pol B.ψ B.emb) {φ : GlobalTheory.UnitaryBC.UA E n → ℂ}
    (hφ : GlobalTheory.UnitaryBC.IsAutFormU φ) {φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (hfin : IsFin M φf) (hne : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0)
    {w : InfinitePlace (maximalRealSubfield E)} {lam' : DomWeight d} (hT : HasType B M om e' f₀ w lam') :
    GlobalTheory.UnitaryBC.HasWeightAt U' (B.emb w).1 lam' := by
  obtain ⟨hirr, i, hi, ⟨x₀, hx₀⟩, hact⟩ := hT
  let Ψ : nablaSq ℂ d lam' → PolData B M := fun x => ⟨pure (i x) φf, pure_mem_pol_pk (hi x) hfin⟩
  have hadd : ∀ x y, Ψ (x + y) = Ψ x + Ψ y := fun x y => Subtype.ext (by
    change pure (i (x + y)) φf = pure (i x) φf + pure (i y) φf
    rw [map_add, pure_add'_pk])
  have hsm : ∀ (a : ℂ) x, Ψ (a • x) = a • Ψ x := fun a x => Subtype.ext (by
    change pure (i (a • x)) φf = a • pure (i x) φf
    rw [map_smul, pure_smul'_pk])
  refine ⟨hirr, { toFun := fun x => pr (Θ (Ψ x) φ), map_add' := fun x y => ?_, map_smul' := fun a x => ?_ }, ?_,
    fun x => (hp _ (hΘ _ _ hφ).2.1).1, fun k x => ?_⟩
  · simp only [hadd, map_add, LinearMap.add_apply]
  · simp only [hsm, map_smul, LinearMap.smul_apply, RingHom.id_apply]
  · intro h0
    apply hne
    have h1 := LinearMap.congr_fun h0 x₀
    have h2 : Ψ x₀ = ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ := Subtype.ext (by
      change pure (i x₀) φf = pure f₀ φf
      rw [hx₀])
    simpa [h2] using h1
  · obtain ⟨Φ₁, h1, h2⟩ := (hΘ (Ψ x) φ hφ).2.2 1 k.1
    have e1 : Φ₁ = Ψ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) x) := Subtype.ext (by
      rw [h1, map_one]
      exact PositivityTheory.ThKG.Loc.Cone.pure_real (hact k.1 k.2 x) φf hfin.1 (_root_.UpperTheory.TP.std_of_fin_k hP hfin))
    rw [map_one, Module.End.one_apply, e1] at h2
    change pr (Θ (Ψ _) φ) = GlobalTheory.UnitaryBC.RU E d k.1 (pr (Θ (Ψ x) φ))
    rw [← (hp _ (hΘ (Ψ x) φ hφ).2.1).2 k.1, ← h2]
    rfl
end Main
section Split
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
private theorem read_point_pk {a : ℕ} {Y : Spc (maximalRealSubfield E) E a} {ε : GlobalTheory.UnitaryBC.UA E a ≃ₜ* UA (cj E) Y.J} (hε : IsBr Y ε)
    (hc : IsCMExt (maximalRealSubfield E) E (cj E)) {v : Pl (maximalRealSubfield E)}
    (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v) (g : GL (Fin a) (Fv (maximalRealSubfield E) v)) :
    ∃ x : GlobalTheory.UnitaryBC.locU a (splitPrime t), ε x.1 ∈ UAt (cj E) Y (evFin (maximalRealSubfield E) v) ∧
      g.1 = (mat (ε x.1)).map (piW t) ∧
      GlobalTheory.UnitaryBC.cLoc (splitPrime t) x.1 = Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g := by
  obtain ⟨x, hx⟩ := cLoc_surj_pk a (splitPrime t) (isSplit_prime_pk hc t) (Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g)
  have hx' : GlobalTheory.UnitaryBC.cLoc (splitPrime t) x.1 = Matrix.GeneralLinearGroup.map (complMap (splitPrime_under t)) g := hx
  refine ⟨x, ?_, ?_, hx'⟩
  · have h1 := (hε.loc (splitPrime t) x.1).2 x.2
    rw [splitPrime_under] at h1
    exact GlobalTheory.ThK.Dbl.Inert.mem_locGrp h1
  · have h1 := hε.spl v t x.1
    rw [hx'] at h1
    have hinj : Function.Injective (complMap (splitPrime_under t)) := (complMap (splitPrime_under t)).injective
    exact Matrix.map_injective hinj h1.symm
end Split
section Split2
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n d : ℕ}
  {B : Base (maximalRealSubfield E) E} {X : Spc (maximalRealSubfield E) E n} {W : Spc (maximalRealSubfield E) E d}
  {M : Model (cj E) X W} {χX χW : Chr (maximalRealSubfield E) E} {om : Rep (cj E) X W}
  {e : GlobalTheory.UnitaryBC.UA E n ≃ₜ* UA (cj E) X.J} {e' : GlobalTheory.UnitaryBC.UA E d ≃ₜ* UA (cj E) W.J}
theorem split_part_k (T : _root_.UpperTheory.TP.Tools_k) (hA : AbsIso) (hP : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om n 0 d 0) (he : IsBr X e) (he' : IsBr W e')
    (Θ : PolData B M →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E n → ℂ) →ₛₗ[starRingEnd ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ))
    (hΘ : ∀ (Φ : PolData B M) φ, GlobalTheory.UnitaryBC.IsAutFormU φ → Θ Φ φ = lift M om Φ.1 (φ ∘ e.symm) ∘ e' ∧ GlobalTheory.UnitaryBC.IsAutFormU (Θ Φ φ) ∧
      ∀ g h, ∃ Φ₁ : PolData B M, Φ₁.1 = om (e g, e' h) Φ.1 ∧
        Θ Φ₁ (GlobalTheory.UnitaryBC.RU E n g φ) = GlobalTheory.UnitaryBC.RU E d h (Θ Φ φ))
    {U : Submodule ℂ (GlobalTheory.UnitaryBC.UA E n → ℂ)} {U' : Submodule ℂ (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    {pr : (GlobalTheory.UnitaryBC.UA E d → ℂ) →ₗ[ℂ] (GlobalTheory.UnitaryBC.UA E d → ℂ)}
    (hU : GlobalTheory.UnitaryBC.IsAutRepU U) (hU' : GlobalTheory.UnitaryBC.IsAutRepU U')
    (hp : ∀ f, GlobalTheory.UnitaryBC.IsAutFormU f → pr f ∈ U' ∧ ∀ x, pr (GlobalTheory.UnitaryBC.RU E d x f) = GlobalTheory.UnitaryBC.RU E d x (pr f))
    {f₀ : SInf (maximalRealSubfield E) (Fin n × Fin d)} (hf₀ : f₀ ∈ M.Pol B.ψ B.emb) {φ : GlobalTheory.UnitaryBC.UA E n → ℂ}
    (hφ : φ ∈ U) {φf : ∀ v : Pl (maximalRealSubfield E), (Fin n × Fin d → Fv (maximalRealSubfield E) v) → ℂ}
    (hfin : IsFin M φf) (hne : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0)
    {v : Pl (maximalRealSubfield E)} (t : E →ₐ[maximalRealSubfield E] Fv (maximalRealSubfield E) v)
    (τ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) ((splitPrime t).adicCompletion E)))
    (τ' : GlobalTheory.CuspRep.SmIrr (GL (Fin d) ((splitPrime t).adicCompletion E)))
    (hτ : CompAt U (splitPrime t) τ) (hτ' : CompAt U' (splitPrime t) τ') : LocPair t χX χW τ τ' := by
  have hc := hP.base.cm
  have hw := isSplit_prime_pk hc t
  let Φ₀ : PolData B M := ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩
  let P : (GlobalTheory.UnitaryBC.UA E n → ℂ) →+ (GlobalTheory.UnitaryBC.UA E d → ℂ) :=
    { toFun := fun y => pr (Θ Φ₀ y), map_zero' := by simp, map_add' := fun a b => by simp }
  obtain ⟨c, p, x₀, hcU, hce, hpe, hp0⟩ := read_pair_pk (splitPrime t) hw hA hU hU' τ τ' hτ hτ' P
    (fun y hy => (hp _ (hΘ _ _ (hU.aut y hy)).2.1).1) hφ hne
  obtain ⟨⟨ι, hι⟩, hSM⟩ := T.split _ E (cj E) B n d X W M χX χW om n 0 d 0 hP v t
  have hSM := hSM ι hι
  have hbij : Set.BijOn ι (SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) : Set _)
      (SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) : Set _) := Model.IsLin.bij hι
  let ιe : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) ≃ₗ[ℂ] SB (Matrix (Fin n) (Fin d) (Fv (maximalRealSubfield E) v)) :=
    LinearEquiv.ofBijective (ι.restrict fun y hy => hbij.mapsTo hy)
      ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
        obtain ⟨a, ha, hab⟩ := hbij.surjOn b.2
        exact ⟨⟨a, ha⟩, Subtype.ext hab⟩⟩
  have hfu : ∀ ψ : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v), IsFin M (Function.update φf v ψ.1) :=
    fun ψ => isFin_update_pk hfin v ψ.2
  let Ψ : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) → PolData B M :=
    fun ψ => ⟨pure f₀ (Function.update φf v ψ.1), pure_mem_pol_pk hf₀ (hfu ψ)⟩
  have hPA := PositivityTheory.ThKF.pureAct (maximalRealSubfield E) (Fin n × Fin d) v id f₀ φf hfin.1 (_root_.UpperTheory.TP.std_of_fin_k hP hfin)
  have hz : pure f₀ (Function.update φf v 0) = 0 :=
    PositivityTheory.ThKG.Loc.Cone.pure_zero f₀ _ (GlobalTheory.PureFactor.update_eventually φf v 0 (_root_.UpperTheory.TP.std_of_fin_k hP hfin)) v (by simp)
  have hadd : ∀ a b, Ψ (a + b) = Ψ a + Ψ b := fun a b => Subtype.ext (by
    have := hPA.2.1 a.1 b.1 1
    rw [one_smul, one_smul] at this
    exact this)
  have hsm : ∀ (r : ℂ) a, Ψ (r • a) = r • Ψ a := fun r a => Subtype.ext (by
    have := hPA.2.1 0 a.1 r
    rw [zero_add, hz, zero_add] at this
    exact this)
  let A : SB (Fin n × Fin d → Fv (maximalRealSubfield E) v) →ₗ[ℂ] τ.V →ₛₗ[starRingEnd ℂ] τ'.V :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun ψ x => p (pr (Θ (Ψ ψ) (c x))))
      (fun a b x => by simp only [hadd, map_add, LinearMap.add_apply])
      (fun r a x => by simp only [hsm, map_smul, LinearMap.smul_apply, RingHom.id_apply])
      (fun a x y => by simp only [map_add])
      (fun r a x => by simp only [map_smul, map_smulₛₗ])
  refine ⟨A ∘ₗ ιe.symm.toLinearMap, ?_, fun g h Φ Φ₁ hΦ x => ?_⟩
  · intro h0
    apply hp0
    have h1 := LinearMap.congr_fun (LinearMap.congr_fun h0 (ιe ⟨φf v, hfin.1 v⟩)) x₀
    have h2 : Ψ ⟨φf v, hfin.1 v⟩ = Φ₀ := Subtype.ext (by
      change pure f₀ (Function.update φf v (φf v)) = pure f₀ φf
      rw [Function.update_eq_self])
    simpa [A, h2, P] using h1
  · obtain ⟨ĝ, hg1, hg2, hg3⟩ := read_point_pk he hc t g
    obtain ⟨ĥ, hh1, hh2, hh3⟩ := read_point_pk he' hc t h
    set ψ := ιe.symm Φ with hψ
    have hιψ : ι ψ.1 = Φ.1 := by
      have := congrArg Subtype.val (ιe.apply_symm_apply Φ)
      exact this
    obtain ⟨ψ₁, ⟨hψ₁, hact⟩, -⟩ := (T.acts _ E (cj E) B n d X W M χX χW om n 0 d 0 hP v).1 _ hg1 _ hh1 ψ.1 ψ.2
    have hι₁ : ι ψ₁ = Φ₁.1 := by
      rw [hΦ, ← hιψ]
      exact hSM _ hg1 _ hh1 g h hg2 hh2 _ ψ.2 _ hψ₁ hact
    have hψ₁' : ιe.symm Φ₁ = ⟨ψ₁, hψ₁⟩ := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext hι₁.symm
    have hΦ₁ := hΘ (Ψ ψ) (c x) (hU.aut _ (hcU x))
    obtain ⟨Φ₂, h1, h2⟩ := hΦ₁.2.2 ĝ.1 ĥ.1
    have hΦ₂ : Φ₂ = Ψ ⟨ψ₁, hψ₁⟩ := Subtype.ext (by
      rw [h1]
      have := (PositivityTheory.ThKF.pureAct (maximalRealSubfield E) (Fin n × Fin d) v (om (e ĝ.1, e' ĥ.1)) f₀ (Function.update φf v ψ.1) (hfu ψ).1
        (_root_.UpperTheory.TP.std_of_fin_k hP (hfu ψ))).2.2 ψ₁ (by simpa using hact)
      refine this.trans ?_
      change pure f₀ (Function.update (Function.update φf v ψ.1) v ψ₁) = pure f₀ (Function.update φf v ψ₁)
      rw [Function.update_idem])
    change p (pr (Θ (Ψ (ιe.symm Φ₁)) (c (τ.ρ _ x)))) = τ'.ρ _ (p (pr (Θ (Ψ ψ) (c x))))
    rw [hψ₁', ← hΦ₂, ← hg3, ← hh3, hce ĝ x, h2, (hp _ hΦ₁.2.1).2, hpe ĥ _ (hp _ hΦ₁.2.1).1]
end Split2
theorem readLift_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.LiftAut_k → AbsIso → _root_.UpperTheory.TP.ReadLift_k := by
  intro T hL hA E _ _ _ B n d X W M χX χW om hP hn e e' he he' U U' pr hU hU' hp f₀ hf₀ φ hφ φf hfin hne
  obtain ⟨Θ, hΘ⟩ := hL E B n d X W M χX χW om hP hn e e' he he'
  have hne' : pr (Θ ⟨pure f₀ φf, pure_mem_pol_pk hf₀ hfin⟩ φ) ≠ 0 := by
    rw [(hΘ ⟨_, pure_mem_pol_pk hf₀ hfin⟩ φ (hU.aut φ hφ)).1]
    exact hne
  exact ⟨fun w lam' hT => _root_.UpperTheory.TP.real_part_k hP Θ hΘ hp hf₀ (hU.aut φ hφ) hfin hne' hT,
    fun v t τ τ' hτ hτ' => _root_.UpperTheory.TP.split_part_k T hA hP he he' Θ hΘ hU hU' hp hf₀ hφ hfin hne' t τ τ' hτ hτ'⟩
end UpperTheory.TP
end
end
end

section
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.TP
theorem tLift_of_tools_k (T : _root_.UpperTheory.TP.Tools_k) (hH : _root_.GlobalTheory.ThK.Dbl.HgtEx_k) : _root_.UpperTheory.TP.TLift_k :=
  _root_.UpperTheory.TP.tLift_of_k T hH brEx (_root_.UpperTheory.TP.hgtFst_k T) (_root_.UpperTheory.TP.realPair_k T)
    (_root_.UpperTheory.TP.nonVan_k T (_root_.UpperTheory.TP.rallis_k T) (_root_.UpperTheory.TP.decomp_k T) (_root_.UpperTheory.TP.bumpAny_k T) (_root_.UpperTheory.TP.datum_k T) (_root_.UpperTheory.TP.tail_k T) absNe (_root_.UpperTheory.TP.schurStep_k T)) (_root_.UpperTheory.TP.liftAut_k T) projEx
    (_root_.UpperTheory.TP.readLift_k T (_root_.UpperTheory.TP.liftAut_k T) absIso)
end UpperTheory.TP
end
end
