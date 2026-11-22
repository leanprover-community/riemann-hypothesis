module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsNormalFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesAgreeAlmostEverywhere
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlacesIffPlaceSetProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovesLocalSuppIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.LocAgree

open GlobalTheory.FinPl GlobalTheory.FinPl.KSplit

variable {D : D7}

theorem latV_le_of_int_smul_on (S : HSp D) (L M : Lat S) (d : ℤ) (hd : d ≠ 0)
    (hLM : ∀ x ∈ L, d • x ∈ M) (R : Pl D → Prop) (hR : ∀ v, R v → ((d : 𝓞 D.host.F)) ∉ v.asIdeal) :
    latV S L R ≤ latV S M R := by
  rw [latV, latMul, AddSubgroup.closure_le]
  rintro y ⟨α, hα, hsupp, a, ha, x, hx, rfl⟩
  rw [Set.mem_singleton_iff] at ha
  subst ha
  apply AddSubgroup.subset_closure
  refine ⟨((d : D.host.F))⁻¹ • α, ?_, ?_, 1, rfl, d • x, hLM x hx, ?_⟩
  · intro w
    rw [map_smul]
    by_cases hw : R w
    · have hval : Valued.v (algebraMap D.host.F (w.adicCompletion D.host.F) (d : D.host.F)) = 1 := by
        have h1 := (w.valuation_eq_one_iff_notMem (K := D.host.F)).mpr (hR w hw)
        have h2 := w.valuedAdicCompletion_eq_valuation' (K := D.host.F) ((d : D.host.F))
        have h4 : (((d : 𝓞 D.host.F)) : D.host.F) = ((d : D.host.F)) :=
          map_intCast (algebraMap (𝓞 D.host.F) D.host.F) _
        exact h2.trans (h4 ▸ h1)
      have hαw := hα w
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hαw ⊢
      rw [Algebra.smul_def, map_mul, map_inv₀, map_inv₀, hval, inv_one, one_mul]
      exact hαw
    · rw [hsupp w hw, smul_zero]
      exact zero_mem _
  · intro w hw
    rw [map_smul, hsupp w hw, smul_zero]
  · funext i
    exact pairA_tmul_int_gen d hd α (x i)

end GlobalTheory.FinPl.LocAgree

end
