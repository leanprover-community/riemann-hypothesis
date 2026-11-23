module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepPrincipalSiegelAdjointOrderAction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_rep_principalSiegel_adjoint_orderAction : ∀ (h' M : ℕ), 1 ≤ h' → 3 ≤ M → Odd M → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (eO : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d₀ : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range eO) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d₀ → ∑ i, ∑ j, W i j • (eO j * bar (eO i)) = (d₀ : O) → ∃ (H : Scheme.{0}) (sH : H ⟶ Sp (cycAway M)) (zH : SiegPre h' M (zetaAway M) sH) (actH : O → (zH.A ⟶ zH.A)), zH.Principal ∧ IsRAct zH.A actH ∧ Adj zH.A zH.P bar actH ∧ IsQProjOver sH ∧ IsLocallyNoetherian H ∧ ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃! g : S ⟶ H, g ≫ sH = t ∧ ActPB z act zH actH g := by
  first | (exact @GlobalTheory.ActSieg.exists_rep) | (exact GlobalTheory.ActSieg.exists_rep) | (intros; apply GlobalTheory.ActSieg.exists_rep  <;> assumption)
