module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_mem_KGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n),
    ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ _ n y
  set P : GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E) (y : GA E n) with hP
  have h1 : ∀ᶠ w in cofinite, ∀ i j, (P.val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact (P.val i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, ((P⁻¹).val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact ((P⁻¹).val i j).2
  filter_upwards [h1, h2] with w hw1 hw2
  have hmul : ∀ (A B : GL (Fin n) (Af E)), A * B = 1 →
      (A.val.map (pLoc E w)) * (B.val.map (pLoc E w)) = 1 := by
    intro A B h
    rw [← Matrix.map_mul, ← Units.val_mul, h, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  let M : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨(P.val i j) w, hw1 i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨((P⁻¹).val i j) w, hw2 i j⟩
  have hM : M.map (Ov E w).subtype = P.val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hN : N.map (Ov E w).subtype = (P⁻¹).val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype) :=
    Matrix.map_injective Subtype.val_injective
  let k : GL (Fin n) (Ov E w) :=
    { val := M
      inv := N
      val_inv := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (mul_inv_cancel P))
      inv_val := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (inv_mul_cancel P)) }
  exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩

end GlobalTheory.BCT.SuppFin
