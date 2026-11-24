module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InfiniteLatticeCovolumeSplitLatticeProd
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

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.infiniteLatticeCovolume_split_lattice_prod : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), Submodule.IsFullLattice E Λ₀ → Submodule.IsFullLattice E Λ' → (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → covAt E (k + 1) (latAt E (k + 1) Λ (oneInf E (k + 1))) = covAt E 1 (latAt E 1 Λ₀ (oneInf E 1)) * covAt E k (latAt E k Λ' (oneInf E k)) :=
  GlobalTheory.CovProd.covAt_latAt_prod
