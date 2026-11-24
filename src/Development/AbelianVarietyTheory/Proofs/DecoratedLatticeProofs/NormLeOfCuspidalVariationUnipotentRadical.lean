module

public import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspGeo

theorem norm_le_of_unipRad_variation : ∀ (D : D7) (V : HSp D) (φ : GA D V → ℂ), IsAutFun V φ → IsCuspFun V φ →
    ∀ (r : ℕ) (C₀ : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C₀ → ∀ (g : GA D V) (e : ℝ),
      (∀ m ∈ NI V C₀, ‖φ (m * g) - φ g‖ ≤ e) → ‖φ g‖ ≤ e := by
  intro D V φ hφ hcusp r C₀ hC g e he
  set 𝔉 := GlobalTheory.Cusp.frameFlag hC with h𝔉
  have hc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA 𝔉) := GlobalTheory.Cusp.cocompact_single _
  have hP := hc.isProbabilityMeasure
  have h0 : GlobalTheory.Cusp.constTerm 𝔉 φ g = 0 :=
    congrFun ((GlobalTheory.Cusp.isCuspFun_iff hφ.left).1 hcusp _ _) g
  have hI := hc.integrable hφ.left hφ.cont g
  have hmem : ∀ n : GlobalTheory.Cusp.NA 𝔉, (n : GA D V) ∈ NI V C₀ := fun n => by
    exact (SetLike.ext_iff.1 (GlobalTheory.Cusp.NA_frameFlag hC) _).1 n.2
  have key : φ g = ∫ q, (φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) := by
    rw [integral_sub (integrable_const _) hI]
    have h0' : ∫ q, φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g) ∂GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉) = 0 := h0
    rw [h0', integral_const]
    simp
  rw [key]
  have hb := norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure (GQ V) (GlobalTheory.Cusp.NA 𝔉))
    (f := fun q => φ g - φ ((q.out : GlobalTheory.Cusp.NA 𝔉) * g)) (C := e)
    (.of_forall fun q => by rw [norm_sub_rev]; exact he _ (hmem _))
  simpa using hb

end GlobalTheory.CuspGeo
