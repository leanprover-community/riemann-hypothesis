module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolUnitNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinPolarisationKernelLeUnitKernel
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

theorem _root_.GlobalTheory.T.zarhin_polarisation_kernel_le_unit_kernel : ∀ (h M d : ℕ), 0 < d → ∀ (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (z : SiegPre (8 * h) M (zetaAway M) t) (act : GlobalTheory.ZarhinFam.ord d → (z.A ⟶ z.A)) (inc : c.A ⟶ z.A) (pr : z.A ⟶ c.A), IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d → z.Principal → IsRAct z.A act → Adj z.A z.P (GlobalTheory.ZarhinFam.bar d) act → IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 c.A → pr ≫ inc = act (GlobalTheory.ZarhinFam.idem d) → LBIso c.P (z.P.pull (inc ⊗ₘ inc).left) → ∀ (T : Over S) (x : T ⟶ c.A), (∃ u : (c.P.pull (lift (snd c.A T ≫ x) (fst c.A T)).left).Gen, u.IsGen) → x ≫ inc ≫ act (GlobalTheory.ZarhinFam.polUnit d) = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (exact GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit) | (intros; apply GlobalTheory.ZarhinFam.ker_pol_le_ker_polUnit  <;> assumption)
