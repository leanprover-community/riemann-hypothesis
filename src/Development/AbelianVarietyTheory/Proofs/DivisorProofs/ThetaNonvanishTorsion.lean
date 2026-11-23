module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

theorem theta_nonvanish_coset (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) (a : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => (a * x).left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ (a * x) τ v ∧ v ≠ 0 :=
  abelianSchemeLaws_all.1.goodPt k P N hN hNk θ hθ a

theorem theta_nonvanish_torsion (k : Type) [Field k] [IsAlgClosed k]
    (P : PolAV (Spec (CommRingCat.of k))) (N : ℕ) (hN : 2 ≤ N) (hNk : (N : k) ≠ 0)
    (θ : LB.Sec (LPow P.A P.L 1 (baseOver (Spec (CommRingCat.of k)))))
    (hθ : SecM.ofSec P.A θ ≠ 0) :
    ∃ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A, x ^ N = 1 ∧
      ∃ (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver (Spec (CommRingCat.of k))).left) (K := Fin 1)
          (fun _ => x.left) (fun _ => 1))) (v : Γ((baseOver (Spec (CommRingCat.of k))).left, ⊤)),
        τ.IsGen ∧ IsValueAt P.A P.L 1 θ x τ v ∧ v ≠ 0 := by
  obtain ⟨x, hx, rest⟩ := theta_nonvanish_coset k P N hN hNk θ hθ 1
  exact ⟨1 * x, by rw [_root_.one_mul]; exact hx, rest⟩

end GlobalTheory.Poinc.Sep
