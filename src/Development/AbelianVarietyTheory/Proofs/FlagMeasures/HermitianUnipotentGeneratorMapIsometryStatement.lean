module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIpowSmulOfSmulMem
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianUnipotentGeneratorMapIsometry
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.HermitianLatticeCounting.S6

theorem _root_.GlobalTheory.T.hermitianUnipotentGeneratorMap_isometry : ∀ {K V ι : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (J : Finset ι) (e ρ : ι → V) (c : ι → ι → K), (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (ρ a) (e b) = 0) → (∀ a b, star (c a b) + c b a + H.B (ρ a) (ρ b) = 0) → ∀ u v : V, H.B (GlobalTheory.RowStab.gen H J e ρ c u) (GlobalTheory.RowStab.gen H J e ρ c v) = H.B u v := by
  first | exact @GlobalTheory.RowStab.gen_isometry | exact GlobalTheory.RowStab.gen_isometry | (intros; apply GlobalTheory.RowStab.gen_isometry <;> assumption)
