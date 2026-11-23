module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ProdMeas

theorem exists_isFinMeas {D : D7} (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) [∀ v, (μf v).IsHaarMeasure]
    (h1 : ∀ᶠ v in cofinite, μf v (Kv V v) = 1) : ∃ ν, IsFinMeas V μf ν := by
  obtain ⟨ν, hν⟩ := (existsUnique_isRestrictedProdFinPts D.sp.cm.sig V.gram (frameLat V) μf h1).exists
  refine ⟨ν, hν.2.2.1, fun ff hf => ?_⟩
  let S := (eventually_cofinite.1 (hf.2.and h1)).toFinset
  have hS : ∀ v ∉ S, ff v = unitLoc _ _ (frameLat V) v ∧ μf v (Kv V v) = 1 := fun v hv => by
    simpa only [S, Finite.mem_toFinset, mem_setOf_eq, not_not] using hv
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ fun v hv => by_contra fun h => hv (by
    rw [(hS v h).1, unitLoc]
    refine (integral_indicator_const _ (isOpen_stabLoc _ _ _ v).measurableSet).trans ?_
    rw [Measure.real, (hS v h).2, ENNReal.toReal_one, one_smul]; rfl)]
  have hcount : Countable (HeightOneSpectrum (𝓞 D.host.F)) := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum _
  have hsf : ∀ w : Empty, SigmaFinite (w.elim : Measure PUnit.{1}) := fun w => w.elim
  have key := (GlobalTheory.RestrMeas.IsCylProd.integral_tensor_indicator (𝕜 := ℂ) (fa := fun w => w.elim) (ff := ff) hν.2.2.2
    (fun w => w.elim) (fun v => ((continuous_proj _ _ v).comp continuous_subtype_val).measurable)
    (fun v => (isOpen_stabLoc _ _ _ v).measurableSet) (fun x => eventually_proj_mem_stabLoc _ _ _ x.1)
    (S := S) (fun v hv => (hS v hv).2) (fun v hv => (hS v hv).1) (fun w => w.elim)
    fun v _ => (hf.1 v).1.continuous.integrable_of_hasCompactSupport (hf.1 v).2).2
  simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul] at key
  exact key

end GlobalTheory.ProdMeas

namespace GlobalTheory.ProdMeas

theorem exists_prod_of_haar : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) →
    (∃ μa, IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ) ∧ ∃ ν, IsFinMeas V μf ν := by
  intro D V μ _ μf hf h1
  haveI := hf
  refine ⟨?_, exists_isFinMeas V μf h1⟩
  obtain ⟨μ₀, h₀⟩ := (existsUnique_isRestrictedProd D.sp.cm.sig V.gram (frameLat V) (fun _ => Measure.haar) μf h1).exists
  haveI := h₀.haar
  have he : μ = Measure.haarScalarFactor μ μ₀ • μ₀ := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : Measure.haarScalarFactor μ μ₀ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at he
    exact (NeZero.ne μ) he
  classical
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace D.host.F))
  rw [he]
  exact ⟨_, h₀.smul_arch w hc⟩

end GlobalTheory.ProdMeas
