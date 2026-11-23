module

public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineExtensions
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.JumpMultiplicityDual
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FilteredIsoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveTensorBcrisToBdR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndepOnOfInvariant
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0Statement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ResBound

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions

namespace GlobalTheory.FontaineExtensionCriteria


open GlobalTheory.Per.FontaineBound in
theorem fontCore_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)
    (K : FinExt l) : LocalSituation.fontCore (P.PD K) := by
  intro LL _ _ _ O _ _ hO A
  have : FiniteDimensional ℚ_[l] LL := hO.2.1
  have hd := ddR_finite_le (P.PD K) (isField_of_tied T) A.ρ
  refine ⟨?_, hd, fun hc => ?_⟩
  · have := isDomain_cris (P.PD K) (isField_of_tied T)
    have := (P.PD K).finK₀
    refine finite_finrank_le (P.PD K).actB (fun b b' hb h => GlobalTheory.T.ratio_invariant_in_K0 l P AI T K b' b hb fun g hg => ?_) A.ρ
    have h1 := h ⟨g, hg⟩
    rw [P.PD_actB, P.PD_actB] at h1
    rw [mul_comm, h1, mul_comm]
  · refine (GlobalTheory.Per.CrisDR.abstract_cmp (P.PD K) A.ρ
      (fun m x hx b hb => GlobalTheory.T.injective_tensor_Bcris_to_BdR l P AI T K m x hx b ?_) hd.1 hd.2 hc).1
    simpa only [P.PD_ι] using hb

theorem strictness_of_tied {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) :
    GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual.Strictness l P :=
  (GlobalTheory.DeRhamCompare.strict_iff P).1 (GlobalTheory.DRFil.deRhamComparison l P AI ⟨T⟩).2.2.2.2.2.1

theorem extCrys_of_tied : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    Nonempty (LocTied l P AI) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineExtensions.ExtCrys P :=
  fun P _ ⟨T⟩ => GlobalTheory.CrysExt.extCrys P (fontCore_of_tied T) (strictness_of_tied T)

end GlobalTheory.FontaineExtensionCriteria
