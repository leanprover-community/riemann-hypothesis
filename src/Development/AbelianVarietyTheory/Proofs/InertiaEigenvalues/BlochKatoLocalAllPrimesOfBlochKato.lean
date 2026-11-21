import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
import Formalism.SharpRestriction.LevelLetterCocycles.RamificationTwoAndConjugationAtQAndD
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IoLMk
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeReductionModPowMemLocConstCocycles

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  first | exact @GlobalTheory.bkADim_of_dimFormula | exact GlobalTheory.bkADim_of_dimFormula | (intros; apply GlobalTheory.bkADim_of_dimFormula <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime]

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {K₀ K : Type} [Field K₀] [Field K]
    [Algebra ℚ_[l] K₀] [Algebra ℚ_[l] K] [Algebra K₀ K] [IsScalarTower ℚ_[l] K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra ℚ_[l] B] [Algebra K₀ B] [IsScalarTower ℚ_[l] K₀ B]
    [Algebra ℚ_[l] BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower ℚ_[l] K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower ℚ_[l] K₀ BdR]
    (PD : PeriodData G ℚ_[l] K₀ K B BdR)

theorem cyclotomicTwist_differential_apply {LL : Type} [Field LL] [Algebra ℚ_[l] LL] (f : G → LL) (x : G × G) :
    ReciprocityTheory.Def.d1 (charRep (cycLL PD LL)) f x =
      algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1 := by
  simp [ReciprocityTheory.Def.d1, charRep, cycLL, Algebra.smul_def]

theorem cobL_iff_trace {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL]
    [FiniteDimensional ℚ_[l] LL] [IsModuleTopology ℚ_[l] LL] (z : G × G → LL) :
    CobL PD z ↔ ∀ c : LL, CobL PD (fun x => Algebra.trace ℚ_[l] LL (c * z x)) := by
  haveI : ContinuousAdd LL := IsModuleTopology.toContinuousAdd ℚ_[l] LL
  haveI : ContinuousSMul ℚ_[l] LL := IsModuleTopology.toContinuousSMul ℚ_[l] LL
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    refine ⟨fun g => Algebra.trace ℚ_[l] LL (c * f g), ?_, ?_⟩
    · exact (IsModuleTopology.continuous_of_linearMap
        ((Algebra.trace ℚ_[l] LL).comp (LinearMap.mulLeft ℚ_[l] c))).comp hf
    · funext x
      rw [cyclotomicTwist_differential_apply, cyclotomicTwist_differential_apply]
      have e1 : c * (algebraMap ℚ_[l] LL (PD.χ x.1 : ℚ_[l]) * f x.2 - f (x.1 * x.2) + f x.1) =
          (PD.χ x.1 : ℚ_[l]) • (c * f x.2) - c * f (x.1 * x.2) + c * f x.1 := by
        rw [Algebra.smul_def]; ring
      rw [e1, map_add, map_sub, map_smul, smul_eq_mul]
      simp
  · intro h
    choose f hf using h
    have hB := traceForm_nondegenerate ℚ_[l] LL
    let b := Module.finBasis ℚ_[l] LL
    let d := (Algebra.traceForm ℚ_[l] LL).dualBasis hB b
    refine ⟨fun g => ∑ i, f (b i) g • d i, ?_, ?_⟩
    · exact continuous_finsetSum _ fun i _ => ((hf (b i)).1).smul continuous_const
    · funext x
      rw [cyclotomicTwist_differential_apply]
      have hz : z x = ∑ i, (d.repr (z x) i) • d i := (d.sum_repr (z x)).symm
      have hc : ∀ i, d.repr (z x) i = (PD.χ x.1 : ℚ_[l]) * f (b i) x.2 - f (b i) (x.1 * x.2) + f (b i) x.1 := by
        intro i
        rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm,
          ← congrFun (hf (b i)).2 x, cyclotomicTwist_differential_apply]
        simp
      rw [hz]
      simp_rw [hc, add_smul, sub_smul, mul_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.smul_sum, Algebra.smul_def]

end Cob

section Main

variable (P : LocPrime l) {K : FinExt l}

def trPair {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) : V →ₗ[ℚ_[l]] V' →ₗ[ℚ_[l]] ℚ_[l] :=
  LinearMap.mk₂ ℚ_[l] (fun x y => Algebra.trace ℚ_[l] LL (Pr x y))
    (fun x x' y => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])
    (fun x y y' => by simp)
    (fun c x y => by simp [LinearMap.map_smul_of_tower])

theorem trPair_apply {LL V V' : Type} [Field LL] [Algebra ℚ_[l] LL]
    [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    (Pr : V →ₗ[LL] V' →ₗ[LL] LL) (x : V) (y : V') :
    trPair Pr x y = Algebra.trace ℚ_[l] LL (Pr x y) := rfl

theorem isDual1_trPair {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
    {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {Pr : V →ₗ[LL] V' →ₗ[LL] LL}
    (hP : IsDual1 (P.PD K) ρ ρ' Pr) : IsDual1 (P.PD K) (resQ ρ) (resQ ρ') (trPair Pr) := by
  have hB := traceForm_nondegenerate ℚ_[l] LL
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨fun g x y => ?_, fun x hx => h2 x fun y => ?_, fun y hy => h3 y fun x => ?_, ?_⟩
  · rw [resQ_apply, resQ_apply, trPair_apply, trPair_apply, h1]
    have e : ((cycLL (P.PD K) LL g : LLˣ) : LL) * Pr x y = ((P.PD K).χ g : ℚ_[l]) • Pr x y := by
      simp [cycLL, Algebra.smul_def]
    rw [e, map_smul, smul_eq_mul]
    simp [cycLL]
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← map_smul]
    exact hx (c • y)
  · refine hB.1 _ fun c => ?_
    rw [Algebra.traceForm_apply, mul_comm, ← smul_eq_mul, ← LinearMap.smul_apply, ← map_smul]
    exact hy (c • x)
  · rw [← Module.finrank_mul_finrank ℚ_[l] LL V, ← Module.finrank_mul_finrank ℚ_[l] LL V', h4]

end Main

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkACore_of_rationalDuality (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l)
    (h : GlobalTheory.Published.BlochKato.RationalDuality (P.PD K)) : bkACore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A A' Pr hdR hP
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : FiniteDimensional ℚ_[l] A'.V := Module.Finite.trans LL A'.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  haveI : IsModuleTopology ℚ_[l] A'.V := isModuleTopology_of_tower ℚ_[l] LL A'.V
  haveI : ContinuousConstSMul ℚ_[l] A.V := ⟨fun c => by
    have hc : Continuous fun x : A.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  haveI : ContinuousConstSMul ℚ_[l] A'.V := ⟨fun c => by
    have hc : Continuous fun x : A'.V => algebraMap ℚ_[l] LL c • x := continuous_const_smul _
    simpa only [algebraMap_smul] using hc⟩
  have key := h A.V A'.V (resQ A.ρ) (resQ A'.ρ) (trPair Pr) A.cont A'.cont
    ((isDR_resQ_iff P A.ρ).mpr hdR) (isDual1_trPair P hP)
  have cupS : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a (c • b) = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cupS' : ∀ (c : LL) (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) (c • a) b = fun x => Algebra.trace ℚ_[l] LL (c * cupL A'.ρ Pr a b x) := by
    intro c a b; funext x
    simp [cupL, trPair_apply]
  have cup1 : ∀ (a : ↥(GK K) → A.V) (b : ↥(GK K) → A'.V),
      cupL (resQ A'.ρ) (trPair Pr) a b = fun x => Algebra.trace ℚ_[l] LL (1 * cupL A'.ρ Pr a b x) := by
    intro a b; funext x
    simp [cupL, trPair_apply]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.1 a ha)]
    constructor
    · intro H b hb
      rw [cobL_iff_trace]
      intro c
      rw [← cupS]
      exact H (c • b) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A'.ρ).smul_mem c hb))
    · intro H b hb
      have := (cobL_iff_trace (P.PD K) _).mp (H b ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp hb)) 1
      rwa [← cup1] at this
  · rw [← mem_finiteCocycles_restrictScalars_Ql P, (key.2 b hb)]
    constructor
    · intro H a ha
      rw [cobL_iff_trace]
      intro c
      rw [← cupS']
      exact H (c • a) ((mem_finiteCocycles_restrictScalars_Ql P _ _).mpr ((finiteCocycles (P.PD K) A.ρ).smul_mem c ha))
    · intro H a ha
      have := (cobL_iff_trace (P.PD K) _).mp (H a ((mem_finiteCocycles_restrictScalars_Ql P _ _).mp ha)) 1
      rwa [← cup1] at this

end GlobalTheory
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.RationalDuality (P.PD K) → bkACore (P.PD K) := by
  atlas_forward_decl GlobalTheory.bkACore_of_rationalDuality
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKTorsionRed

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {ρ : Representation LL G V}

theorem coboundary_mem_blochKato_cocycles (m : V) (hm : Continuous fun g => ρ g m) : (fun g => ρ g m - m) ∈ finiteCocycles PD ρ := by
  refine ⟨⟨?_, fun g h => ?_⟩, m ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · simp_rw [sub_eq_add_neg]
    exact hm.add continuous_const
  · simp only [map_mul, Module.End.mul_apply, map_sub]
    abel
  · simp [actVB, sub_tmul]

def latticeCoboundaryCocycle (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (x : ↥L.T) : ↥(latticeCocycles L) :=
  ⟨fun g => ρ g x - x, Submodule.mem_inf.2 ⟨(coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)).1,
    Submodule.mem_pi.2 fun g _ => L.T.sub_mem (L.stable g x x.2) x.2⟩⟩

theorem lattice_reduction_coboundary_mem_cocycles (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (x : ↥L.T) :
    redT L I (latticeCoboundaryCocycle PD L hρ x) = LinearMap.pi (fun g => actQ L I hI g - LinearMap.id) (I.mkQ x) := by
  funext g
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, Submodule.mkQ_apply, actQ,
    Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub]
  rfl

theorem mem_HfQ_iff (L : Lattice (O := O) ρ) (hρ : ∀ m, Continuous fun g => ρ g m) (I : Submodule O ↥L.T)
    (hI : StableSub L I) (c : G → ↥L.T ⧸ I) :
    c ∈ HfQ PD L I hI ↔ ∃ a : ↥(latticeCocycles L), (a : G → V) ∈ finiteCocycles PD ρ ∧ c = redT L I a := by
  constructor
  · intro h
    obtain ⟨_, ⟨a0, ha0, rfl⟩, _, ⟨xb, rfl⟩, rfl⟩ := Submodule.mem_sup.1 h
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
    refine ⟨a0 + latticeCoboundaryCocycle PD L hρ x, (finiteCocycles PD ρ).add_mem ha0.2 (coboundary_mem_blochKato_cocycles PD (x : V) (hρ x)), ?_⟩
    rw [map_add, lattice_reduction_coboundary_mem_cocycles PD L hρ I hI x]
    rfl
  · rintro ⟨a, ha, rfl⟩
    exact Submodule.mem_sup_left ⟨a, ⟨a.2, ha⟩, rfl⟩

theorem mem_HfQ_iff_red : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  intro l _ P K LL _ _ _ O _ _ _hO A LA ϖ r hI c
  exact mem_HfQ_iff (P.PD K) LA A.cont _ hI c

end GlobalTheory.BKTorsionRed
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ HfQ (P.PD K) LA _ hI ↔ ∃ a : ↥(latticeCocycles LA), (a : ↥(GK K) → A.V) ∈ finiteCocycles (P.PD K) A.ρ ∧ c = redT LA _ a := by
  atlas_forward_decl GlobalTheory.BKTorsionRed.mem_HfQ_iff_red
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (a : ↥(latticeCocycles LA)), redT LA _ a ∈ quotientCocycles LA _ hI := by
  first | exact @GlobalTheory.RedLocConst.redT_mem_Z1Q | exact GlobalTheory.RedLocConst.redT_mem_Z1Q | (intros; apply GlobalTheory.RedLocConst.redT_mem_Z1Q <;> assumption)
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BDLocConst

theorem lattice_divisible_coboundaries_le_locConst_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA c hc
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  haveI : IsTopologicalAddGroup A.V := IsModuleTopology.topologicalAddGroup LL A.V
  obtain ⟨y, rfl⟩ := hc
  induction y using Submodule.Quotient.induction_on with
  | H x =>
  have hval : ∀ g, (LinearMap.pi (fun g => actD LA g - LinearMap.id) (Submodule.Quotient.mk x : A.V ⧸ LA.T)) g
      = Submodule.Quotient.mk (A.ρ g x - x) := by
    intro g
    rfl
  refine ⟨?_, ?_⟩
  · have hT : IsOpen (LA.T : Set A.V) := Formalism.MainNotions.BlochKatoDuality.Br.lat_open hopen LA.T LA.fg LA.span
    have := Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk LA.T hT (fun g => A.ρ g x - x) ((A.cont x).sub continuous_const)
    convert this using 1
    funext g
    exact hval g
  · intro g h
    rw [hval, hval, hval]
    show _ = Submodule.Quotient.mk (A.ρ g x - x) + Submodule.Quotient.mk (A.ρ g (A.ρ h x - x))
    rw [← Submodule.Quotient.mk_add, map_mul]
    congr 1
    simp only [Module.End.mul_apply, map_sub]
    abel

end GlobalTheory.BDLocConst
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), BD LA ≤ divisibleCocycles LA := by
  atlas_forward_decl GlobalTheory.BDLocConst.lattice_divisible_coboundaries_le_locConst_cocycles
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevelCocycle

theorem ioL_actQ {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (g : G)
    (x : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) :
    GlobalTheory.BKFinLevel.ioL L ϖ r (actQ L _ hI g x) = actD L g (GlobalTheory.BKFinLevel.ioL L ϖ r x) := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    simp only [actQ, Submodule.mapQ_apply, GlobalTheory.BKFinLevel.ioL_mk, actD, actT]
    congr 1
    simp only [LinearMap.coe_restrictScalars, map_smul]
    rfl

theorem ioL_mem_Z1D : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ r hI c hc
  refine ⟨hc.1.comp _, fun g h => ?_⟩
  simp only [hc.2 g h, map_add, ioL_actQ]

end GlobalTheory.BKFinLevelCocycle
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), c ∈ quotientCocycles LA _ hI → (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ divisibleCocycles LA := by
  atlas_forward_decl GlobalTheory.BKFinLevelCocycle.ioL_mem_Z1D
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevelKer

theorem mk_eq_of_smul {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
    {ρ : Representation LL G V} (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (π : LL) (hπ : π ≠ 0)
    (hpr : ∀ v : V, π ^ r • v = ϖ ^ r • v) (u v w : V) (hu : u ∈ L.T) (hv : v ∈ L.T)
    (hvw : π⁻¹ ^ r • u - w ∈ L.T) (hyw : v = π ^ r • w) :
    (Submodule.Quotient.mk (⟨v, hv⟩ : ↥L.T) : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) =
      Submodule.Quotient.mk ⟨u, hu⟩ := by
  rw [Submodule.Quotient.eq]
  have ht : (⟨v, hv⟩ : ↥L.T) - ⟨u, hu⟩ = ϖ ^ r • (-(⟨_, hvw⟩ : ↥L.T)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_neg]
    rw [← hpr, smul_neg, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul, hyw]
    abel
  rw [ht]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top

theorem hfQ_of_ioL_mem_HfD : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  intro l _ P K LL _ _ _ O _ _ hO A LA ϖ hϖ r hI c hc
  obtain ⟨π, hπdef⟩ : ∃ π : LL, π = algebraMap O LL ϖ := ⟨_, rfl⟩
  have hπ : π ≠ 0 := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, -, -⟩ := hO
    haveI := hDom; haveI := hDVR; haveI := hFr
    intro h
    exact hϖ.ne_zero (IsFractionRing.injective O LL (by rw [← hπdef, h, map_zero]))
  clear hO

  obtain ⟨_, ⟨z, hz, rfl⟩, _, ⟨xq, rfl⟩, hsum⟩ := Submodule.mem_sup.1 hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xq
  obtain ⟨w, hwdef⟩ : ∃ w : ↥(GK K) → A.V, w = z + fun g => A.ρ g x - x := ⟨_, rfl⟩
  have hcob : (fun g => A.ρ g x - x) ∈ finiteCocycles (P.PD K) A.ρ := by
    refine ⟨⟨?_, fun g h => ?_⟩, x ⊗ₜ[ℚ_[l]] (1 : _), fun g => ?_⟩
    · simp_rw [sub_eq_add_neg]
      exact (A.cont x).add continuous_const
    · simp only [map_mul, Module.End.mul_apply, map_sub]
      abel
    · simp [actVB, sub_tmul]
  have hw : w ∈ finiteCocycles (P.PD K) A.ρ := hwdef ▸ (finiteCocycles (P.PD K) A.ρ).add_mem hz hcob

  choose ch hch using fun g => Submodule.Quotient.mk_surjective _ (c g)

  have hpt : ∀ g, (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g ∈ LA.T := by
    intro g
    have key : GlobalTheory.BKFinLevel.ioL LA ϖ r (c g) = Submodule.Quotient.mk (p := LA.T) (w g) :=
      by rw [← congrFun hsum g, hwdef]; rfl
    have h2 : (Submodule.Quotient.mk (π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) : A.V ⧸ LA.T) =
        Submodule.Quotient.mk (w g) :=
      hπdef ▸ (GlobalTheory.BKFinLevel.ioL_mk LA ϖ r (ch g)).symm.trans ((congrArg _ (hch g)).trans key)
    exact (Submodule.Quotient.eq _).1 h2
  obtain ⟨y, hydef⟩ : ∃ y : ↥(GK K) → A.V, y = fun g => π ^ r • w g := ⟨_, rfl⟩
  have hyf : y ∈ finiteCocycles (P.PD K) A.ρ := by
    have h := (finiteCocycles (P.PD K) A.ρ).smul_mem (π ^ r) hw
    subst hydef; exact h
  have hpr : ∀ v : A.V, π ^ r • v = ϖ ^ r • v := fun v => by
    rw [hπdef, ← map_pow, algebraMap_smul]
  have hyT : ∀ g, y g ∈ LA.T := by
    intro g
    have : y g = ((ch g : ↥LA.T) : A.V) - ϖ ^ r • ((π⁻¹ ^ r • ((ch g : ↥LA.T) : A.V)) - w g) := by
      rw [← hpr, smul_sub, smul_smul, ← mul_pow, mul_inv_cancel₀ hπ, one_pow, one_smul]
      simp [hydef]
    rw [this]
    exact LA.T.sub_mem (ch g).2 (LA.T.smul_mem _ (hpt g))
  have hyZ : y ∈ latticeCocycles LA := ⟨hyf.1, fun g _ => hyT g⟩
  refine Submodule.mem_sup_left ⟨⟨y, hyZ⟩, ⟨hyZ, hyf⟩, ?_⟩
  funext g
  have e : (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) ⟨y, hyZ⟩) g =
      Submodule.Quotient.mk (⟨y g, hyT g⟩ : ↥LA.T) := rfl
  rw [e, ← hch g]
  exact mk_eq_of_smul LA ϖ r π hπ hpr _ _ (w g) (ch g).2 (hyT g) (hpt g) (by rw [hydef])

end GlobalTheory.BKFinLevelKer
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_quotient_of_divisible_image_mem : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (c : ↥(GK K) → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (c g)) ∈ HfD (P.PD K) LA → c ∈ HfQ (P.PD K) LA _ hI := by
  atlas_forward_decl GlobalTheory.BKFinLevelKer.hfQ_of_ioL_mem_HfD
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKFinLevel.NatCup

section Lifts

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I x ∈ L.T :=
  (Submodule.Quotient.mk_surjective I x).choose.2

theorem mk_liftQ_lat (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (x : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ L I x, liftQ_mem_lat L I x⟩ : ↥L.T ⧸ I) = x :=
  (Submodule.Quotient.mk_surjective I x).choose_spec

theorem mk_liftD_lat (L : Lattice (O := O) ρ) (c : V ⧸ L.T) :
    (Submodule.Quotient.mk (liftD L c) : V ⧸ L.T) = c :=
  (Submodule.Quotient.mk_surjective L.T c).choose_spec

theorem mem_span_pow_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by simp [hr]⟩
    · exact ⟨0, by simp [h0, zero_pow hr.ne']⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow, map_one]⟩

theorem pair_shift {V' : Type} [AddCommGroup V'] [Module LL V'] (m : V →ₗ[LL] V' →ₗ[LL] LL)
    (f : V' →ₗ[LL] V') (a t â : V) (w y : V') (c π k u v : LL) (hâ : â = a + π • t)
    (hk : c * π = k) (hu : m a (f (w - c • y)) = u) (hv : m t (f y) = v) :
    u - k * v = m a (f w) - c * m â (f y) := by
  subst hâ hk hu hv
  simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

end Lifts

end GlobalTheory.BKFinLevel.NatCup

namespace GlobalTheory.BKFinLevel

open GlobalTheory.BKFinLevel.NatCup in

theorem cobO_cupLD_ioL_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  intro l _ P K LL _ _ _ O _ _ _ L1 hL1 A A' LA LA' m hd ϖ r d c'
  have key : ∀ x, (Submodule.Quotient.mk (cupLD LA' m (d : ↥(GK K) → A.V)
      (fun g => ioL LA' ϖ r (c' g)) x) : LL ⧸ L1.T) =
      Submodule.Quotient.mk (cupQ LA LA' m ϖ r (redT LA _ d) c' x) := by
    rintro ⟨g, h⟩
    rw [Submodule.Quotient.eq, hL1]
    obtain ⟨e, he⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r

    have hyT := liftQ_mem_lat LA' _ (c' h)
    have hw : liftD LA' (ioL LA' ϖ r (c' h)) -
        (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h) ∈ LA'.T := by
      have h2 : ioL LA' ϖ r (c' h) = Submodule.Quotient.mk
          ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)) := by
        conv_lhs => rw [← mk_liftQ_lat LA' _ (c' h)]
        rfl
      exact (Submodule.Quotient.eq _).1 ((mk_liftD_lat LA' _).trans h2)

    have haT : (d : ↥(GK K) → A.V) g ∈ LA.T := d.2.2 g (Set.mem_univ g)
    have hred : (Submodule.Quotient.mk ⟨Formalism.MainNotions.LocalSituation.liftQ LA _ (redT LA _ d g),
        liftQ_mem_lat LA _ _⟩ : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) =
        Submodule.Quotient.mk ⟨(d : ↥(GK K) → A.V) g, haT⟩ := mk_liftQ_lat LA _ _
    obtain ⟨t, ht⟩ := (mem_span_pow_smul_top LA _ _).1 ((Submodule.Quotient.eq _).1 hred)
    have ht' : Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g) =
        (d : ↥(GK K) → A.V) g + (algebraMap O LL ϖ) ^ r • (t : A.V) := by
      have := congrArg (fun z : ↥LA.T => (z : A.V)) ht
      simp only [Submodule.coe_sub, Submodule.coe_smul] at this
      have hs : (algebraMap O LL ϖ) ^ r • (t : A.V) = ϖ ^ r • (t : A.V) := by
        rw [← map_pow, algebraMap_smul]
      rw [hs]
      exact (sub_eq_iff_eq_add').1 this
    have hw2 : A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hw
    have hy2 : A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h)) ∈ LA'.T := LA'.stable g _ hyT
    have hb1' : ∃ b : O, m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)) - (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hw2 _ haT
    have hb2' : ∃ b : O, m (t : A.V) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T) (c' h))) = algebraMap O LL b := (hd.2 _).1 hy2 _ t.2
    obtain ⟨b1, hb1⟩ := hb1'
    obtain ⟨b2, hb2⟩ := hb2'
    refine ⟨b1 - e * b2, ?_⟩
    show algebraMap O LL (b1 - e * b2) =
      m ((d : ↥(GK K) → A.V) g) (A'.ρ g (liftD LA' (ioL LA' ϖ r (c' h)))) -
        (algebraMap O LL ϖ)⁻¹ ^ r * m (Formalism.MainNotions.LocalSituation.liftQ LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) (redT LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T) d g))
          (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h)))
    have hsplit : algebraMap O LL (b1 - e * b2) =
        algebraMap O LL b1 - algebraMap O LL e * algebraMap O LL b2 := by
      rw [map_sub, map_mul]
    exact hsplit.trans (pair_shift m (A'.ρ g) _ _ _ _ _ _ _ _ _ _ ht' he hb1 hb2)
  unfold CobO
  exact Iff.of_eq (congrArg (fun z => z ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤) (funext key))

end GlobalTheory.BKFinLevel
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (d : ↥(latticeCocycles LA)) (c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => GlobalTheory.BKFinLevel.ioL LA' ϖ r (c' g))) ↔ CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r (redT LA _ d) c') := by
  atlas_forward_decl GlobalTheory.BKFinLevel.cobO_cupLD_ioL_iff
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKSwapCup

section Gen
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem liftQ_mem (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    Formalism.MainNotions.LocalSituation.liftQ L I q ∈ L.T :=
  (Submodule.Quotient.mk_surjective I q).choose.2

theorem mk_liftQ (L : Lattice (O := O) ρ) (I : Submodule O ↥L.T) (q : ↥L.T ⧸ I) :
    (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L I q, liftQ_mem L I q⟩ : ↥L.T) : ↥L.T ⧸ I) = q :=
  (Submodule.Quotient.mk_surjective I q).choose_spec

theorem liftQ_sub (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (x : ↥L.T)
    (q : ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (hq : Submodule.Quotient.mk x = q) :
    ∃ t ∈ L.T, Formalism.MainNotions.LocalSituation.liftQ L _ q - (x : V) = (algebraMap O LL ϖ) ^ r • t := by
  have h : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x ∈
      (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T) :=
    (Submodule.Quotient.eq _).1 ((mk_liftQ L _ q).trans hq.symm)
  generalize hy : (⟨Formalism.MainNotions.LocalSituation.liftQ L _ q, liftQ_mem L _ q⟩ : ↥L.T) - x = y at h
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h
  obtain ⟨t, -, ht⟩ := h
  subst ht
  refine ⟨t, t.2, ?_⟩
  rw [← map_pow, algebraMap_smul, ← Submodule.coe_smul, ← hy]
  rfl

theorem inv_pow_mul_pow_mem (ϖ : O) (r : ℕ) :
    ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * (algebraMap O LL ϖ) ^ r = algebraMap O LL e := by
  rcases eq_or_ne (algebraMap O LL ϖ) 0 with h | h
  · rcases Nat.eq_zero_or_pos r with hr | hr
    · exact ⟨1, by subst hr; simp⟩
    · exact ⟨0, by rw [h, zero_pow hr.ne', mul_zero, map_zero]⟩
  · exact ⟨1, by rw [← mul_pow, inv_mul_cancel₀ h, one_pow, map_one]⟩

end Gen
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cong
variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def swapF (L : Lattice (O := O) ρ) (P : V →ₗ[LL] V' →ₗ[LL] LL) (ϖ : O) (r : ℕ)
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (d : G → V') (g : G) : LL :=
  (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)

theorem swap_cong (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') (P : V →ₗ[LL] V' →ₗ[LL] LL)
    (hint : ∀ x ∈ L.T, ∀ y ∈ L'.T, ∃ e : O, P x y = algebraMap O LL e)
    (χ : G → LL) (hχ : ∀ g x y, P (ρ g x) (ρ' g y) = χ g * P x y) (ϖ : O) (r : ℕ)
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (s : G → ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T))
    (hs : ∀ g h, s (g * h) = s g + actQ L _ hI g (s h))
    (d : G → V') (hdT : ∀ g, d g ∈ L'.T) (hdmul : ∀ g h, d (g * h) = d g + ρ' g (d h))
    (q : G → ↥L'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L'.T))
    (hq : ∀ h, Submodule.Quotient.mk (⟨d h, hdT h⟩ : ↥L'.T) = q h) (g h : G) :
    ∃ e : O, GlobalTheory.BKFinLevel.cupQ L L' P ϖ r s q (g, h)
      + cupLD L P.flip d (fun g => GlobalTheory.BKFinLevel.ioL L ϖ r (s g)) (g, h)
      + (χ g * swapF L P ϖ r s d h - swapF L P ϖ r s d (g * h) + swapF L P ϖ r s d g)
      = algebraMap O LL e := by
  have huT : ∀ g, Formalism.MainNotions.LocalSituation.liftQ L _ (s g) ∈ L.T := fun g => liftQ_mem L _ (s g)
  have hmk : ∀ g, (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s g :=
    fun g => mk_liftQ L _ (s g)

  have hq3 : (Submodule.Quotient.mk (⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s g), huT g⟩ +
      actT L g ⟨Formalism.MainNotions.LocalSituation.liftQ L _ (s h), huT h⟩ : ↥L.T) :
      ↥L.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) = s (g * h) := by
    rw [hs g h]
    exact (Submodule.Quotient.mk_add _).trans
      (congrArg₂ (· + ·) (hmk g) (congrArg (actQ L _ hI g) (hmk h)))
  obtain ⟨t3, ht3, hu3⟩ := liftQ_sub L ϖ r _ _ hq3

  obtain ⟨t1, ht1, hd1⟩ := liftQ_sub L' ϖ r _ _ (hq h)

  have hio : GlobalTheory.BKFinLevel.ioL L ϖ r (s h) =
      Submodule.Quotient.mk ((algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) :=
    (congrArg (GlobalTheory.BKFinLevel.ioL L ϖ r) (mk_liftQ L _ (s h))).symm.trans
      (GlobalTheory.BKFinLevel.ioL_mk L ϖ r _)
  have hl : (Submodule.Quotient.mk (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))) : V ⧸ L.T) =
      GlobalTheory.BKFinLevel.ioL L ϖ r (s h) :=
    (Submodule.Quotient.mk_surjective L.T _).choose_spec
  have ht2 := (Submodule.Quotient.eq _).1 (hl.trans hio)
  show ∃ e : O, (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (ρ' g (Formalism.MainNotions.LocalSituation.liftQ L' _ (q h)))
      + P.flip (d g) (ρ g (liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h))))
      + (χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h))
        - (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h))) (d (g * h))
        + (algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s g)) (d g)) = algebraMap O LL e
  generalize liftD L (GlobalTheory.BKFinLevel.ioL L ϖ r (s h)) = w at ht2 ⊢
  obtain ⟨t2, ht2', rfl⟩ : ∃ t2 ∈ L.T,
      w = (algebraMap O LL ϖ)⁻¹ ^ r • Formalism.MainNotions.LocalSituation.liftQ L _ (s h) + t2 :=
    ⟨_, ht2, by abel⟩
  have E1 : Formalism.MainNotions.LocalSituation.liftQ L' _ (q h) = d h + (algebraMap O LL ϖ) ^ r • t1 :=
    sub_eq_iff_eq_add'.1 hd1
  have E3 : Formalism.MainNotions.LocalSituation.liftQ L _ (s (g * h)) = Formalism.MainNotions.LocalSituation.liftQ L _ (s g) +
      ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) + (algebraMap O LL ϖ) ^ r • t3 :=
    sub_eq_iff_eq_add'.1 hu3
  obtain ⟨e0, he0⟩ := inv_pow_mul_pow_mem (LL := LL) ϖ r
  obtain ⟨e1, he1⟩ := hint _ (huT g) _ (L'.stable g _ ht1)
  obtain ⟨e2, he2⟩ := hint _ (L.stable g _ ht2') _ (hdT g)
  obtain ⟨e3, he3⟩ := hint t3 ht3 (d g + ρ' g (d h)) (by rw [← hdmul]; exact hdT _)
  refine ⟨e0 * e1 + e2 - e0 * e3, ?_⟩
  have E5 : χ g * ((algebraMap O LL ϖ)⁻¹ ^ r * P (Formalism.MainNotions.LocalSituation.liftQ L _ (s h)) (d h)) =
      (algebraMap O LL ϖ)⁻¹ ^ r * P (ρ g (Formalism.MainNotions.LocalSituation.liftQ L _ (s h))) (ρ' g (d h)) := by
    rw [hχ]; ring
  rw [E1, E3, hdmul, E5]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    LinearMap.flip_apply] at he3 ⊢
  rw [map_sub, map_add, map_mul, map_mul, ← he0, ← he1, ← he2, ← he3]
  ring

end Cong
end GlobalTheory.BKSwapCup

namespace GlobalTheory.BKSwapCup

section Cob

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem cobO_swap (hopen : IsOpen (Set.range (algebraMap O LL)))
    (L1 : Lattice (O := O) (charRep (cycLL PD LL)))
    (hL1 : L1.T = LinearMap.range (Algebra.linearMap O LL)) {A A' : GRep G Qp LL O}
    (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL)
    (hm : IsDualLat1 PD LA LA' m) (ϖ : O) (r : ℕ)
    (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T))
    (s : G → ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hs : s ∈ quotientCocycles LA _ hI)
    (d : ↥(latticeCocycles LA')) :
    CobO PD L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔
      CobO PD L1 (cupLD LA m.flip (d : G → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  have hdT : ∀ g, (d : G → A'.V) g ∈ LA'.T := fun g => d.2.2 g (Set.mem_univ g)
  have hint : ∀ x ∈ LA.T, ∀ y ∈ LA'.T, ∃ e : O, m x y = algebraMap O LL e :=
    fun x hx y hy => (hm.2 y).1 hy x hx
  have key := swap_cong LA LA' m hint (fun g => ((cycLL PD LL g : LLˣ) : LL)) hm.1.1 ϖ r hI s
    hs.2 (d : G → A'.V) hdT d.2.1.2 (redT LA' _ d) (fun _ => rfl)
  let Fq : G → LL ⧸ L1.T := fun g =>
    Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)
  have hFq : Fq ∈ ReciprocityTheory.Def.C1 G (⊤ : Submodule O (LL ⧸ L1.T)) := by
    refine ⟨?_, fun _ => Submodule.mem_top⟩
    have hT : IsOpen (L1.T : Set LL) := by rw [hL1]; exact hopen
    have hu : Continuous fun g => Formalism.MainNotions.LocalSituation.liftQ LA _ (s g) :=
      (hs.1.comp (Formalism.MainNotions.LocalSituation.liftQ LA _)).continuous
    have hc : Continuous (swapF LA m ϖ r s (d : G → A'.V)) :=
      continuous_const.mul ((IsModuleTopology.continuous_bilinear_of_finite_left m).comp
        (hu.prodMk d.2.1.1))
    exact Formalism.MainNotions.BlochKatoDuality.Br.locConst_mk L1.T hT _ hc
  have hD : ReciprocityTheory.Def.d1 (repD L1) Fq ∈ ReciprocityTheory.Def.B2 (repD L1) ⊤ := ⟨Fq, hFq, rfl⟩
  have heq : (fun x => (Submodule.Quotient.mk
      (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) x) : LL ⧸ L1.T)) =
      -((fun x => (Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
        (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) x) : LL ⧸ L1.T)) +
          ReciprocityTheory.Def.d1 (repD L1) Fq) := by
    funext x
    obtain ⟨g, h⟩ := x
    obtain ⟨e, he⟩ := key g h
    show (Submodule.Quotient.mk (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d) (g, h)) :
        LL ⧸ L1.T) = -(Submodule.Quotient.mk (cupLD LA m.flip (d : G → A'.V)
          (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g)) (g, h)) +
        (Submodule.Quotient.mk (((cycLL PD LL g : LLˣ) : LL) * swapF LA m ϖ r s (d : G → A'.V) h)
          - Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) (g * h))
          + Submodule.Quotient.mk (swapF LA m ϖ r s (d : G → A'.V) g)))
    rw [eq_neg_iff_add_eq_zero, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add,
      ← Submodule.Quotient.mk_add, ← Submodule.Quotient.mk_add, ← add_assoc, he,
      Submodule.Quotient.mk_eq_zero, hL1]
    exact ⟨e, rfl⟩
  unfold CobO
  rw [heq, neg_mem_iff, Submodule.add_mem_iff_left _ hD]

end Cob

theorem cobO_cupQ_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hm ϖ r hI s hs d
  obtain ⟨-, -, -, htr, hopen⟩ := hO
  haveI := htr
  exact cobO_swap (P.PD K) hopen L1 hL1 LA LA' m hm ϖ r hI s hs d

end GlobalTheory.BKSwapCup
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_level_cup_swap_coboundary_iff : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), ∀ s ∈ quotientCocycles LA _ hI, ∀ d : ↥(latticeCocycles LA'), CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r s (redT LA' _ d)) ↔ CobO (P.PD K) L1 (cupLD LA m.flip (d : ↥(GK K) → A'.V) (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r (s g))) := by
  atlas_forward_decl GlobalTheory.BKSwapCup.cobO_cupQ_iff
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BKOrthRed

section Gen

variable {G : Type} [Group G] {LL : Type} [Field LL] {O : Type} [CommRing O] [Algebra O LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

theorem mem_span_smul_top (L : Lattice (O := O) ρ) (a : O) (x : ↥L.T) :
    x ∈ (Ideal.span {a} • ⊤ : Submodule O ↥L.T) ↔ ∃ y : ↥L.T, x = a • y := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, rfl⟩; exact ⟨y, rfl⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, Submodule.mem_top, rfl⟩

theorem liftQ_eq (L : Lattice (O := O) ρ) (ϖ : O) (r : ℕ) (v : V) (hv : v ∈ L.T) :
    ∃ t : ↥L.T, Formalism.MainNotions.LocalSituation.liftQ L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
      (Submodule.Quotient.mk ⟨v, hv⟩) = v + (algebraMap O LL ϖ) ^ r • (t : V) := by
  have hs := (Submodule.Quotient.mk_surjective (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)
    (Submodule.Quotient.mk ⟨v, hv⟩)).choose_spec
  obtain ⟨t, ht⟩ := (mem_span_smul_top L _ _).1 ((Submodule.Quotient.eq _).1 hs)
  refine ⟨t, ?_⟩
  have h2 := congrArg (fun x : ↥L.T => (x : V)) ht
  simp only [Submodule.coe_sub, Submodule.coe_smul] at h2
  unfold Formalism.MainNotions.LocalSituation.liftQ
  rw [← map_pow, algebraMap_smul, ← h2]
  abel

end Gen

section Gal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O LL]
    [IsFractionRing O LL]

theorem hfQ_lift {A : GRep G Qp LL O} (LA : Lattice (O := O) A.ρ) (I : Submodule O ↥LA.T)
    (hI : StableSub LA I) (c : G → ↥LA.T ⧸ I) (hc : c ∈ HfQ PD LA I hI) :
    ∃ a : G → A.V, a ∈ finiteCocycles PD A.ρ ∧ ∀ g, ∃ h : a g ∈ LA.T, c g = Submodule.Quotient.mk ⟨a g, h⟩ := by
  rw [HfQ, Submodule.mem_sup] at hc
  obtain ⟨y, hy, z, hz, rfl⟩ := hc
  obtain ⟨a0, ha0, rfl⟩ := hy
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨xh, rfl⟩ := Submodule.Quotient.mk_surjective I x
  refine ⟨(a0 : G → A.V) + cob A.ρ (xh : A.V), (finiteCocycles PD A.ρ).add_mem ha0.2 (Formalism.MainNotions.BlochKatoDuality.Br.coboundary_mem_finite_cocycles PD A _),
    fun g => ⟨LA.T.add_mem (a0.2.2 g trivial) (LA.T.sub_mem (LA.stable g _ xh.2) xh.2), ?_⟩⟩
  show Submodule.Quotient.mk (evT LA g a0) + (actQ LA I hI g (Submodule.Quotient.mk xh) - Submodule.Quotient.mk xh) = _
  rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_add]
  congr 1

end Gal

theorem cupQ_cobO_of_bkA : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  intro l _ P K hA LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI' c hc c' hc'
  have hA' := hA LL O hO
  obtain ⟨⟨hDom, hDVR, hFr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hDom; haveI := hDVR; haveI := hFr; haveI := htr
  obtain ⟨a, ha, hag⟩ := hfQ_lift (P.PD K) LA _ hI c hc
  obtain ⟨b, hb, hbg⟩ := hfQ_lift (P.PD K) LA' _ hI' c' hc'
  obtain ⟨f, hf, hfd1⟩ := ((hA' A A' m hDR hd.1).1 a ha.1).1 ha b hb
  set s : LL := (algebraMap O LL ϖ)⁻¹ ^ r with hs
  have hcob : CobL (P.PD K) (fun x => s * cupL A'.ρ m a b x) := by
    refine ⟨s • f, continuous_const.mul hf, ?_⟩
    rw [map_smul, hfd1]
    rfl
  have hred := Formalism.MainNotions.BlochKatoDuality.Br.red_cob (P.PD K) hopen L1 hL1 _ hcob
  refine (Formalism.MainNotions.BlochKatoDuality.Br.cobO_congr (P.PD K) L1 _ _ ?_).2 hred
  rintro ⟨g, h⟩
  obtain ⟨hag1, hcg⟩ := hag g
  obtain ⟨hbh1, hch⟩ := hbg h
  obtain ⟨t, ht⟩ := liftQ_eq LA ϖ r (a g) hag1
  obtain ⟨t', ht'⟩ := liftQ_eq LA' ϖ r (b h) hbh1
  obtain ⟨u1, hu1⟩ := (hd.2 _).1 (LA'.stable g _ hbh1) t t.2
  obtain ⟨u2, hu2⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) (a g) hag1
  obtain ⟨u3, hu3⟩ := (hd.2 _).1 (LA'.stable g _ t'.2) t t.2
  have ho : ∃ o : O, algebraMap O LL o = s * (algebraMap O LL ϖ) ^ r := by
    rw [hs, ← mul_pow]
    rcases eq_or_ne (algebraMap O LL ϖ) 0 with h0 | h0
    · exact ⟨0 ^ r, by rw [h0, inv_zero, zero_mul, map_pow, map_zero]⟩
    · exact ⟨1, by rw [inv_mul_cancel₀ h0, one_pow, map_one]⟩
  obtain ⟨o, ho⟩ := ho
  rw [Submodule.Quotient.eq, hL1]
  refine ⟨o * (u1 + u2 + ϖ ^ r * u3), ?_⟩
  show _ = s * m (Formalism.MainNotions.LocalSituation.liftQ LA _ (c g)) (A'.ρ g (Formalism.MainNotions.LocalSituation.liftQ LA' _ (c' h))) - s * m (a g) (A'.ρ g (b h))
  rw [hcg, hch, ht, ht']
  simp only [Algebra.linearMap_apply, map_mul, map_add, map_pow, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul]
  rw [← hu1, ← hu2, ← hu3, ho]
  ring

end GlobalTheory.BKOrthRed
end
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), Formalism.MainNotions.N.bkACore (P.PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDR (P.PD K) A.ρ → IsDualLat1 (P.PD K) LA LA' m → ∀ (ϖ : O) (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)), ∀ c ∈ HfQ (P.PD K) LA _ hI, ∀ c' ∈ HfQ (P.PD K) LA' _ hI', CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c') := by
  atlas_forward_decl GlobalTheory.BKOrthRed.cupQ_cobO_of_bkA
end

section
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BKFinLevel

theorem bkC_of_bkA_bkB : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  intro hT _ l _ P _ _ K hA hB LL _ _ _ O _ _ hO L1 hL1 A A' LA LA' m hDR hd ϖ hϖ r hI hI'
  show (∀ c ∈ quotientCocycles LA _ hI, (c ∈ HfQ (P.PD K) LA _ hI ↔ ∀ c' ∈ HfQ (P.PD K) LA' _ hI',
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c'))) ∧
    (∀ c' ∈ quotientCocycles LA' _ hI', (c' ∈ HfQ (P.PD K) LA' _ hI' ↔ ∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')))
  have orth := GlobalTheory.T.blochKato_reductions_orthogonal_mod_pow l P K hA LL O hO L1 hL1 A A' LA LA' m hDR hd ϖ r hI hI'

  have hfz : ∀ s ∈ HfQ (P.PD K) LA _ hI, s ∈ quotientCocycles LA _ hI := by
    intro s hs
    obtain ⟨a, -, has⟩ := (GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI s).1 hs
    rw [has]
    exact GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A LA ϖ hϖ r hI a

  have clause2 : ∀ c' ∈ quotientCocycles LA' _ hI', (∀ c ∈ HfQ (P.PD K) LA _ hI,
      CobO (P.PD K) L1 (GlobalTheory.BKFinLevel.cupQ LA LA' m ϖ r c c')) → c' ∈ HfQ (P.PD K) LA' _ hI' := by
    intro c' hc' horth
    apply GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A' LA' ϖ hϖ r hI' c'
    have hZ := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A' LA' ϖ r hI' c' hc'
    refine ((hB LL O hO L1 hL1 A A' LA LA' m hDR hd).1 _ hZ).2 ?_
    intro d hdf
    have hdT : d ∈ latticeCocycles LA := hdf.1
    rw [GlobalTheory.T.cup_divisible_image_coboundary_iff_finite_level l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r ⟨d, hdT⟩ c']
    exact horth _ ((GlobalTheory.T.mem_blochKato_quotient_pow_iff_reduction l P K LL O hO A LA ϖ r hI _).2 ⟨⟨d, hdT⟩, hdf.2, rfl⟩)
  refine ⟨fun c hc => ⟨fun h c' hc' => orth c h c' hc', fun h => ?_⟩,
    fun c' hc' => ⟨fun h c hc => orth c hc c' h, clause2 c' hc'⟩⟩

  let S : Submodule O (↥(GK K) → A.V ⧸ LA.T) :=
    (HfQ (P.PD K) LA _ hI).map ((GlobalTheory.BKFinLevel.ioL LA ϖ r).compLeft ↥(GK K)) ⊔ BD LA
  have hS1 : BD LA ≤ S := le_sup_right
  have hS2 : S ≤ divisibleCocycles LA := by
    refine sup_le ?_ (GlobalTheory.T.lattice_divisible_coboundaries_le_locConst_cocycles' l P K LL O hO A LA)
    rintro _ ⟨s, hs, rfl⟩
    exact GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI s (hfz s hs)
  have hflip : IsDualLat1 (P.PD K) LA' LA m.flip := by
    obtain ⟨⟨hDom, hDVR, hFr⟩, -, -, htr, -⟩ := id hO
    exact Formalism.MainNotions.BlochKatoDuality.Br.isDualLat1_flip (P.PD K) hd
  have hC := GlobalTheory.T.latticeQuotientToDivisibleQuotient_mem_cocycles l P K LL O hO A LA ϖ r hI c hc
  have key := GlobalTheory.T.lattice_dual_cyclotomic hT l P K LL O hO L1 hL1 A' A LA' LA m.flip hflip S hS1 hS2 _ hC (by
    intro d hdZ hdS
    rw [← GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI c hc ⟨d, hdZ⟩]
    apply h
    apply clause2 _ (GlobalTheory.T.lattice_reduction_mod_pow_mem_locConst_cocycles l P K LL O hO A' LA' ϖ hϖ r hI' ⟨d, hdZ⟩)
    intro s hs
    rw [GlobalTheory.T.finite_level_cup_swap_coboundary_iff l P K LL O hO L1 hL1 A A' LA LA' m hd ϖ r hI s (hfz s hs) ⟨d, hdZ⟩]
    exact hdS _ (Submodule.mem_sup_left ⟨s, hs, rfl⟩))
  obtain ⟨y, ⟨a, ha, rfl⟩, z, hz, hyz⟩ := Submodule.mem_sup.1 key
  have hdiff : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) ∈ HfD (P.PD K) LA := by
    have : (fun g => GlobalTheory.BKFinLevel.ioL LA ϖ r ((c - a) g)) = z := by
      funext g
      have := congrFun hyz g
      simp only [Pi.sub_apply, map_sub, LinearMap.compLeft_apply, Function.comp_apply,
        Pi.add_apply] at this ⊢
      rw [← this]; abel
    rw [this]
    exact Submodule.mem_sup_right hz
  have := GlobalTheory.T.blochKato_quotient_of_divisible_image_mem l P K LL O hO A LA ϖ hϖ r hI _ hdiff
  simpa using (HfQ (P.PD K) LA _ hI).add_mem this ha

end GlobalTheory.BKFinLevel
end

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  atlas_forward_decl GlobalTheory.BKFinLevel.bkC_of_bkA_bkB
end

section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality l P K hInt
  exact ⟨hA, GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
end
