module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalSymLiftMulOdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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

theorem _root_.GlobalTheory.T.universal_symLift_mul_odd : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (N : ℕ), Odd N → ∀ (T : Over Xo.X) (a b : T ⟶ Xo.univ.t.G) (Ua Ub Uab : ThetaGrp Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T) (e : Γ(T.left, ⊤)ˣ), SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) a Ua → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) b Ub → SymLift Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (N ^ 2) (a * b) Uab → WeilIs Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) a b e → ∃ r : Γ(T.left, ⊤)ˣ, r ^ 2 = e ∧ r ^ (N ^ 2) = 1 ∧ ∀ s s₁ s₂ s₃ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) T), IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ub s s₁ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Ua s₁ s₂ → IsActOf Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) Uab s s₃ → ∀ j, s₂.f j = liftFun Xo.univ.t.G _ (r : Γ(T.left, ⊤)) * s₃.f j := by
  first | exact @GlobalTheory.moduli_univ_symLift_mul | exact GlobalTheory.moduli_univ_symLift_mul | (intros; apply GlobalTheory.moduli_univ_symLift_mul <;> assumption)
