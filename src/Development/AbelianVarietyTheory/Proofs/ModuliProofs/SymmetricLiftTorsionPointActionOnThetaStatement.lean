module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLiftTorsionPointActionOnTheta
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.symmetricLift_torsionPoint_action_on_theta : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (N : ℕ) (l : u.Λ) (f : (Fin P.g → ℂ) → ℂ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T) (x : T ⟶ P.A) (U : Out.ThetaGrp P.A P.L ((N : ℤ) ^ 2) T) (s s' : LB.Sec (Out.LPow P.A P.L ((N : ℤ) ^ 2) T)), u.IsAH Hm χ → Odd N → p ≫ x = u.ex (((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ)) → Out.SymLift P.A P.L ((N : ℤ) ^ 2) (N ^ 2) x U → Out.IsActOf P.A P.L ((N : ℤ) ^ 2) U s s' → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s.f j) = f z * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) → (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L ((N : ℤ) ^ 2) T).U j) (s'.f j) = (χ l * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm l l - Real.pi * hermForm Hm z l) * f (z + ((N : ℂ) ^ 2)⁻¹ • (l : Fin P.g → ℂ))) * u.fr (j 0) z ^ (((N : ℤ) ^ 2) : ℤ)) := by
  first | exact @GlobalTheory.symLift_act_in_frame | exact GlobalTheory.symLift_act_in_frame | (intros; apply GlobalTheory.symLift_act_in_frame <;> assumption)
