module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.MulConjTransposeEqOneOfOrthonormal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopMinorWedge

theorem det_mul_sub {n l : ℕ} (A : Matrix (Fin l) (Fin n) ℂ) (B : Matrix (Fin n) (Fin l) ℂ) :
    (A * B).det = ∑ I : BranchingSupport.Sub n l, (A.submatrix id (I.1.orderEmbOfFin I.2)).det *
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det := by
  rw [GlobalTheory.det_mul_eq_sum_minors]
  exact Fintype.sum_equiv
    (⟨fun S => ⟨S.1, S.2⟩, fun S => ⟨S.1, S.2⟩, fun _ => rfl, fun _ => rfl⟩ :
      Set.powersetCard (Fin n) l ≃ BranchingSupport.Sub n l) _ _ (fun _ => rfl)

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := det_mul_sub (g.submatrix (I.1.orderEmbOfFin I.2) id) (Matrix.of fun c b => f b c)
  have h2 : BranchingSupport.wedge (fun b => g *ᵥ f b) I =
      (g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun c b => f b c)).det := rfl
  rw [h2, h]
  rfl

theorem star_wedge_dot {n l : ℕ} (f f' : Fin l → Fin n → ℂ) :
    star (BranchingSupport.wedge f) ⬝ᵥ BranchingSupport.wedge f' = (Matrix.of fun a b => star (f a) ⬝ᵥ f' b).det := by
  have h := det_mul_sub (Matrix.of fun a c => star (f a c)) (Matrix.of fun c b => f' b c)
  have h2 : (Matrix.of fun a b => star (f a) ⬝ᵥ f' b) =
      (Matrix.of fun a c => star (f a c)) * (Matrix.of fun c b => f' b c) := rfl
  rw [h2, h]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [Pi.star_apply, BranchingSupport.wedge, ← Matrix.det_conjTranspose]
  rfl

theorem herm_cmp_wedge_eq_det : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (cmp (r + 1) g *ᵥ wedge (Formalism.QuantumDeterminants.fvec k r z'))
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (Formalism.QuantumDeterminants.Zhat k r z z' g).det := by
  intro k r z z' g
  rw [Formalism.QuantumDeterminants.herm, cmp_mulVec_wedge, cmp_mulVec_wedge, star_wedge_dot]
  rfl

end GlobalTheory.TopMinorWedge
