module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscGaugeCompletionBasicProperties
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.closedDiscGaugeCompletion_basic_properties : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (u : A) (ρ : ℝ≥0), IsUltrametricDist (Disc l u ρ) ∧ (∀ y : Disc l u ρ, ‖((l : ℕ) : Disc l u ρ) * y‖ = ‖y‖ / l) ∧ (∀ (N : Type) [NormedAddCommGroup N], (∀ z : N, l • z = 0 → z = 0) → ∀ F G : Disc l u ρ →+ N, Continuous F → Continuous G → (∀ a, F (toDisc l u ρ a) = G (toDisc l u ρ a)) → F = G) ∧ ∀ (A' A'' : Type) [CommRing A'] [CommRing A''] (u' : A') (u'' : A'') (ρ' ρ'' : ℝ≥0) (f : A →+* A') (f' : A' →+* A'') (F : Disc l u ρ →+* Disc l u' ρ') (F' : Disc l u' ρ' →+* Disc l u'' ρ''), IsDiscMap (l := _) (u := _) (ρ := _) f F → IsDiscMap (l := _) (u := _) (ρ := _) f' F' → IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) := by
  first | exact @GlobalTheory.BSP.DiscBasic.disc_basic | exact GlobalTheory.BSP.DiscBasic.disc_basic | (intros; apply GlobalTheory.BSP.DiscBasic.disc_basic <;> assumption)
