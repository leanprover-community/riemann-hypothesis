module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareIntegrableSmoothSubmoduleGL
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap

@[expose] public section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem rt_mem_l2Sub_and_inner_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N) (hx : x ∈ squareIntegrableSmoothSubmoduleGL μ) (hy : y ∈ squareIntegrableSmoothSubmoduleGL μ) :
    rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  have key : ∀ z : Sm E N, ∀ hz : z ∈ squareIntegrableSmoothSubmoduleGL μ, ∃ h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ,
      l2Map μ (rt E N g z) = R (latticeGL E N) μ g (l2Map μ z) := by
    intro z hz
    have h' : rt E N g z ∈ squareIntegrableSmoothSubmoduleGL μ := ((mem_l2Sub μ).1 hz).mul_right g
    refine ⟨h', ?_⟩
    rw [l2Map_apply μ h', l2Map_apply μ hz, right_translate_toL2]
    rfl
  obtain ⟨hx', ex⟩ := key x hx
  obtain ⟨hy', ey⟩ := key y hy
  refine ⟨hx', ?_⟩
  let U : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g).toLinearMap, norm_R g⟩
  rw [ex, ey]
  exact U.inner_map_map _ _

end GlobalTheory.CompanionTheory.FinDiscOrth
