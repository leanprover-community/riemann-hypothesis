module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

@[expose] public section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePairNormalForm_geometry_summary : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), NFFull N.F N.F' N.j N.j_le N.c ∧ IsLift N.F N.F' N.Wt ∧ IsCompl N.Wt N.Pi ∧ Module.finrank K N.Wt + 2 * r + 1 = Module.finrank K V ∧ N.Wn = N.Wt ⊔ Submodule.span K {N.F.z} ∧ uPerp N.F N.F' = N.Wn ⊔ II N.F N.F' ∧ wSp N.F N.F' = N.Wt ⊔ II N.F N.F' ∧ wSp N.F' N.F = wSp N.F N.F' ∧ GlobalTheory.Mass.PD (GlobalTheory.Mass.hRes H.B.flip N.Wt) ∧ 1 ≤ N.T ∧ N.nD N.j ≠ 0 ∧ N.Pi = V0 N.F N.F' ⊔ N.Ist := by
  first | exact @GlobalTheory.DegCnt.NF.geometry | exact GlobalTheory.DegCnt.NF.geometry | (intros; apply GlobalTheory.DegCnt.NF.geometry <;> assumption)
