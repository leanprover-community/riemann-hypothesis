module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValIotaLeOfMem
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnitRepresentativesSplitPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler

theorem _root_.GlobalTheory.T.exists_local_unit_representatives_split_prime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : HeightOneSpectrum (OF E)) (P : HeightOneSpectrum (𝓞 E)), Splits q → Over P q → ∃ R : Finset (P.adicCompletion E)ˣ, R.card + 1 = Ideal.absNorm q.asIdeal ∧ (∀ r ∈ R, Valued.v (r : P.adicCompletion E) = 1) ∧ ∀ y : (Af E)ˣ, (∀ P', Over P' q → Valued.v ((y : Af E) P') = 1) → ∃! r, r ∈ R ∧ LocIn 1 q (((single P r)⁻¹ * y : (Af E)ˣ) : Af E) := by
  first | exact @GlobalTheory.CMVal.Euler.Resid.exists_representatives | exact GlobalTheory.CMVal.Euler.Resid.exists_representatives | (intros; apply GlobalTheory.CMVal.Euler.Resid.exists_representatives <;> assumption)
