module

public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.CenteredPerpendicularSets
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon
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

@[expose] public section

open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

theorem _root_.GlobalTheory.T.exists_stabilizerNilradicalIntegral_lift_of_orthogonal : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)), R ≤ perpIn I x R → ∀ Φ : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ R, Φ *ᵥ y = 0) → (∀ y ∈ perpIn I x R, Φ *ᵥ y ∈ R) → ∃ Y ∈ nilInt I x R, ∀ y ∈ perpIn I x R, Y *ᵥ y = Φ *ᵥ y := by
  first | exact @GlobalTheory.NilLift.exists_nilInt_lift | exact GlobalTheory.NilLift.exists_nilInt_lift | (intros; apply GlobalTheory.NilLift.exists_nilInt_lift <;> assumption)
