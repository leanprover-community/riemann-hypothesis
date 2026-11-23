module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CechLogFormsFrobeniusLift
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.cech_log_forms_frobenius_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  first | exact @_root_.GlobalTheory.DI.decomp_of_isLifted | exact _root_.GlobalTheory.DI.decomp_of_isLifted | (intros; apply _root_.GlobalTheory.DI.decomp_of_isLifted <;> assumption)
