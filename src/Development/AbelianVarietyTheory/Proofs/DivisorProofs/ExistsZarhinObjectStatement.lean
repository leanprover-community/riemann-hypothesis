module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormMulTransposeMulFormInvMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsZarhinObject
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_principal_zarhin_object_of_siegKerBy : ∀ (h M d : ℕ), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → ∃ (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin (8 * h) ⊕ Fin (8 * h) → ℤ)) (n : ℕ) (o : Fin n → GlobalTheory.ZarhinFam.ord d) (κ : Fin n → (Fin (8 * h) ⊕ Fin (8 * h) → ℤ) →+ (Fin h ⊕ Fin h → ℤ)), ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → ∃ (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)), z.Principal ∧ IsRAct z.A act ∧ Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act ∧ ZRel (GlobalTheory.ZarhinFam.idem d) jl o κ c z act := by
  first | (exact @GlobalTheory.ZarhinFam.exists_zarhin_object) | (exact GlobalTheory.ZarhinFam.exists_zarhin_object) | (intros; apply GlobalTheory.ZarhinFam.exists_zarhin_object  <;> assumption)
