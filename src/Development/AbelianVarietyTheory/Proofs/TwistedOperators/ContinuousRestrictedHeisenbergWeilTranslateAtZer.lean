module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousMovPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ResHeisCont

theorem continuous_res_heisO : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ u : WO V W, Continuous fun p : GA D V × GA D W => res V V' W C B μ 𝓨 (heisO ψ V W u (ω p f)) 0 := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 h𝓨 f hf u
  have hψ := hω.std.1
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D V).1
  haveI := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, h𝓨.2.2]; exact ENNReal.one_lt_top⟩
  have hy : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B 0 := by
    unfold isoPart
    exact (continuous_id.matrix_mul continuous_const).add continuous_const
  refine continuous_iff_continuousAt.2 fun p₀ => ?_
  obtain ⟨K, hK, hKn⟩ := exists_compact_mem_nhds p₀
  obtain ⟨c, hc⟩ := GlobalTheory.WeilSupBound.exists_sup_bound D ψ V W χS χT ω hω f hf K hK
  unfold res
  refine continuousAt_of_dominated (bound := fun _ => c) ?_ ?_ (integrable_const c) ?_
  · exact Filter.Eventually.of_forall fun p =>
      ((GlobalTheory.HeisOrtho.continuous_heisO hψ (hω.om_pres p f hf).cont u).comp hy).aestronglyMeasurable
  · filter_upwards [hKn] with p hp
    exact Filter.Eventually.of_forall fun y => by
      rw [GlobalTheory.HeisOrtho.norm_heisO hψ]; exact hc p hp _
  · refine Filter.Eventually.of_forall fun y => ?_
    unfold heisO
    exact (continuous_const.mul (hω.om_cont f hf _)).continuousAt

end GlobalTheory.ResHeisCont

end
