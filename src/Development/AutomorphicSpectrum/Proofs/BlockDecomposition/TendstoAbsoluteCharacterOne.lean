module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem absFn_tendsto_one : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (x : GA E N) (w : ℕ → ℂ), Tendsto w atTop (𝓝 0) → Tendsto (fun k => absFn N (w k) x) atTop (𝓝 1) := by
  intro E _ _ _ N x w hw
  have hL : ∀ t : ℂ, absFn N t x =
      Complex.exp (t * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)) := by
    intro t
    exact GlobalTheory.Mem.Chr.CharModel.absHom_val E t (GeneralLinearGroup.det x)
  have h0 : Tendsto (fun k => Complex.exp (w k *
      (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ))) atTop
      (𝓝 (Complex.exp (0 * (GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x) : ℝ)))) :=
    (Complex.continuous_exp.tendsto _).comp (hw.mul_const _)
  simpa [hL] using h0

end GlobalTheory.CompanionTheory.LimV
