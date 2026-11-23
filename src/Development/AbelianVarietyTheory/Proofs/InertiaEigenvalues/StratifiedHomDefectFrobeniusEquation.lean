module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTwoHomsERegularAssociatedStatement
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

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.HomDefect

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {r : R} (hr : r ∈ nonZeroDivisors R)
    {M N : Matrix m n R} (h : r • M = r • N) : M = N := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hr).1 this

theorem map_smul' {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (φ : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map φ = φ c • M.map φ := by
  ext i j; simp

theorem map_frob {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B : Obj l ↥(OL K)} (f : Hom bk.prism B)
    {m n : Type} (M : Matrix m n bk.S) : (M.map (frobS l bk.a)).map (BK.hf f) = (M.map (BK.hf f)).map B.D.φ := by
  ext i j
  exact f.f_φ (M i j)

end GlobalTheory.BSP.HomDefect



open GlobalTheory.BSP.HomDefect in
theorem GlobalTheory.BSP.strat_homDefect_φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  intro l _ K bk d d' S S' Y hY B f g
  obtain ⟨hfE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨hgE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B g f
  have hYf := congrArg (fun M => M.map (BK.hf f)) hY
  have hYg := congrArg (fun M => M.map (BK.hf g)) hY
  simp only [map_smul', Matrix.map_mul, map_pow, map_frob] at hYf hYg
  have e1 := S.ε_φ f g
  have e2 := S'.ε_φ f g
  have T1 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hgE S'.a)
    calc BK.hf g bk.E ^ S'.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf g bk.E ^ S'.a • (S'.A.map (BK.hf f) * (S'.ε f g).map B.D.φ)) * (Y.map (BK.hf g)).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (S'.ε f g * S'.A.map (BK.hf g))) * (Y.map (BK.hf g)).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (Y.map (BK.hf g)).map B.D.φ)) e2
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (S'.ε f g * M)) hYg
      _ = BK.hf g bk.E ^ S'.a • BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  have T2 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hfE S.a)
    calc BK.hf f bk.E ^ S.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S.a • (S'.A.map (BK.hf f) * (Y.map (BK.hf f)).map B.D.φ)) * (S.ε f g).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.A.map (BK.hf f))) * (S.ε f g).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (S.ε f g).map B.D.φ)) hYf
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf g bk.E ^ S.a • (S.A.map (BK.hf f) * (S.ε f g).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf f bk.E ^ S.a • (S.ε f g * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * M)) e1
      _ = BK.hf f bk.E ^ S.a • BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_sub]
  · exact congrArg₂ (· - ·) T1 T2
  · exact fun a b => map_sub _ a b
