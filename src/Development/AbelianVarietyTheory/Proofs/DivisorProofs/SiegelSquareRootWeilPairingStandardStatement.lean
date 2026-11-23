module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSquareRootWeilPairingStandard
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
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM GlobalTheory.KeyFam

theorem _root_.GlobalTheory.T.siegel_square_root_weil_pairing_standard : ∀ (h k : ℕ) (K : Type) [Field K] (ζ : K) (σ : K →+* ℂ) (S : Scheme.{0}) (s : S ⟶ Sp K) (c : SiegPre h k ζ s) (p : Sp ℂ ⟶ S) (P : Out.PolAV (Sp ℂ)) (φ : P.A.left ⟶ c.A.left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), 3 ≤ k → Odd k → σ ζ = Complex.exp (-(2 * Real.pi * Complex.I) / k) → p ≫ s = spMap σ → SqOf P c p φ → (∀ a, (lev a).left ≫ φ = p ≫ (c.lev a).left) → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ k = 1) → ∀ (a b : Fin h ⊕ Fin h → ℤ) (e : ℂˣ), (e : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (omegaStd a b : ℂ) / k) → Out.WeilIs P.A P.L k (lev a) (lev b) (unitOn e) := by
  first | exact @GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | exact GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf | (intros; apply GlobalTheory.SqRootPairing.weilIs_lev_of_sqOf <;> assumption)
