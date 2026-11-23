module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Dchart
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterization
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.lieEntries_unipotentBesselN_characterization : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (Nset k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → unrealify x i j = 0)) ∧ (x ∈ lieE (Nset k r) → NormedSpace.exp (unrealify x) ∈ Nset k r) := by
  first | exact @GlobalTheory.CellDens.LieN.lieE_Nset | exact GlobalTheory.CellDens.LieN.lieE_Nset | (intros; apply GlobalTheory.CellDens.LieN.lieE_Nset <;> assumption)
