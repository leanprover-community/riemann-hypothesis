module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameMatrixChartRatios
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

@[expose] public section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem _root_.GlobalTheory.T.frame_matrix_chart_ratios : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (S : Type) [Fintype S] (r n : S → ℕ) (κ : Type) (x : κ → Ω) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (c₀ : κ), x c₀ ≠ 0 → (∀ a : Ω, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c₀), h ≠ 0 ∧ a = g / h) → (∀ s, ∃ B : Matrix (Fin (r s)) (Fin (n s)) Ω, B * Matrix.of (fun j l => φ s j (c s l)) = 1) → ∃ J₀ : FlagIx κ n r, flagCoord κ x φ c J₀ ≠ 0 ∧ ∀ a : GenField Ω r, ∃ g ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), ∃ h ∈ Algebra.adjoin ℤ (Set.range fun j => flagCoord κ x φ c j / flagCoord κ x φ c J₀), h ≠ 0 ∧ a = g / h := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | exact GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.CoordGen.flagCoord_generate <;> assumption)
