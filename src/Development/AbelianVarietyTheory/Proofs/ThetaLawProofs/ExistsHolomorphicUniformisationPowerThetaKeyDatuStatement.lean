module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by
  first | exact @GlobalTheory.PowUnif.exists_holUnif_pow | exact GlobalTheory.PowUnif.exists_holUnif_pow | (intros; apply GlobalTheory.PowUnif.exists_holUnif_pow <;> assumption)
