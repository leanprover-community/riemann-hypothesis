module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular
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

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

theorem _root_.GlobalTheory.T.chart_frame_matrix_regular : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 → g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧ locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) = ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing <;> assumption)
