module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorNormalisedMulByNIso
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

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_generator_normalised_mulByN_iso : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), S.Over₀ M U₀ → ∀ (n : ℕ) (α : LB.Gen (LB.LinComb ρ.P.L (K := Fin 2) ![𝟙 ρ.P.A.left, (mulA ρ.P.A n).left] ![((n : ℕ) : ℤ) ^ 2, -1])), α.IsGen → IsNormMul ρ.P.A ρ.P.L ρ.rig n α → ∃ κ, κ.IsGen ∧ Q.MulRel n α κ := by
  first | exact @GlobalTheory.ZH.MulExtend.exists_gen_mulRel | exact GlobalTheory.ZH.MulExtend.exists_gen_mulRel | (intros; apply GlobalTheory.ZH.MulExtend.exists_gen_mulRel <;> assumption)
