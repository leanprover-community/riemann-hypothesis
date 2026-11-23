module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
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

theorem UpperTheory.building_fixed_points_equiv :
    UpperTheory.V.Af.BA.FixEquiv := by
  intro A B _ _ i σ N hi hσ
  have hmem : ∀ g : GL (Fin N) A, Matrix.GeneralLinearGroup.map (n := Fin N) i g ∈
      (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) := by
    intro g
    change Matrix.GeneralLinearGroup.map (n := Fin N) σ (Matrix.GeneralLinearGroup.map (n := Fin N) i g) =
      Matrix.GeneralLinearGroup.map (n := Fin N) i g
    ext a b
    exact (hσ _).2 ⟨g a b, rfl⟩
  have hM : ∀ X Y : Matrix (Fin N) (Fin N) A, X.map i = Y.map i → X = Y := by
    intro X Y h
    ext a b
    exact hi (congrFun (congrFun h a) b)
  have hpre : ∀ g : GL (Fin N) B,
      g ∈ (Matrix.GeneralLinearGroup.map (n := Fin N) σ).eqLocus (MonoidHom.id _) →
      ∃ X : Matrix (Fin N) (Fin N) A, X.map i = (g : Matrix (Fin N) (Fin N) B) := by
    intro g hg
    have hg' : Matrix.GeneralLinearGroup.map (n := Fin N) σ g = g := hg
    have h1 : ∀ a b, ∃ x : A, i x = (g : Matrix (Fin N) (Fin N) B) a b := by
      intro a b
      refine (hσ _).1 ?_
      have := congrArg (fun k : GL (Fin N) B => (k : Matrix (Fin N) (Fin N) B) a b) hg'
      exact this
    choose X hX using h1
    exact ⟨Matrix.of X, by ext a b; exact hX a b⟩
  refine ⟨(MulEquiv.ofBijective
    ((Matrix.GeneralLinearGroup.map (n := Fin N) i).codRestrict _ hmem) ⟨?_, ?_⟩).symm⟩
  · intro g k h
    have h1 : Matrix.GeneralLinearGroup.map (n := Fin N) i g =
      Matrix.GeneralLinearGroup.map (n := Fin N) i k := congrArg Subtype.val h
    apply Units.ext
    apply hM
    exact congrArg Units.val h1
  · rintro ⟨g, hg⟩
    obtain ⟨X, hX⟩ := hpre g hg
    obtain ⟨Y, hY⟩ := hpre g⁻¹ (inv_mem hg)
    refine ⟨⟨X, Y, hM _ _ ?_, hM _ _ ?_⟩, ?_⟩
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.mul_inv
    · rw [Matrix.map_mul, hX, hY, Matrix.map_one _ (map_zero i) (map_one i)]
      exact g.inv_mul
    · apply Subtype.ext
      apply Units.ext
      exact hX
