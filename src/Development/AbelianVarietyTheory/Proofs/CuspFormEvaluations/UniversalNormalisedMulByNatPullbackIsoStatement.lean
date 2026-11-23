module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalNormalisedMulByNatPullbackIso
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
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.universal_normalised_mulByNat_pullback_iso : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), ∃ α₀ : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![𝟙 Xo.univ.t.G.left, (mulA Xo.univ.t.G N).left] ![(N : ℤ) ^ 2, -1]), α₀.IsGen ∧ IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₀ ∧ (∀ α₁, α₁.IsGen → IsNormMul Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig N α₁ → LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α₁ α₀) ∧ ∀ T : Over Xo.X, ∃ α : LB.Gen (LB.LinComb Xo.univ.t.PP.L (K := Fin 2) ![(snd T Xo.univ.t.G).left, (snd T Xo.univ.t.G ^ N).left] ![(N : ℤ) ^ 2, -1]), α.IsGen ∧ LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _ α (LB.pullGen Xo.univ.t.PP.L _ _ α₀ (snd T Xo.univ.t.G).left) := by
  first | exact @GlobalTheory.moduli_univ_normMul | exact GlobalTheory.moduli_univ_normMul | (intros; apply GlobalTheory.moduli_univ_normMul <;> assumption)
