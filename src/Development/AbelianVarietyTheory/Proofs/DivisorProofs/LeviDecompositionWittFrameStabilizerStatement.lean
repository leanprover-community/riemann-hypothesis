module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviDecompositionWittFrameStabilizer
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
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

@[expose] public section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

theorem _root_.GlobalTheory.T.leviDecomposition_wittFrameStabilizer : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ p β, ScalesBy σ J X p β → ∃ u ∈ unipRad σ J X, ∃ m ∈ GlobalTheory.StdPar.levi σ J X Y {Fin.last r}, p = u * m ∧ ScalesBy σ J X m β ∧ (p ∈ ratPts σ J → m ∈ ratPts σ J) ∧ (absE F E (Matrix.GeneralLinearGroup.det β) = 1 → m ∈ GlobalTheory.StdPar.leviOne σ J X Y {Fin.last r}) := by
  first | exact @GlobalTheory.LeviDecompositionFrame.levi_dec_frame | exact GlobalTheory.LeviDecompositionFrame.levi_dec_frame | (intros; apply GlobalTheory.LeviDecompositionFrame.levi_dec_frame <;> assumption)
