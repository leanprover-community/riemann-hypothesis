module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIdTorusEltOne
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus
theorem isIdTorusElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}
    (ha : IsIdTorusElt σ J X Y l a) (hb : IsIdTorusElt σ J X Y l' b) : IsIdTorusElt σ J X Y (l * l') (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp))
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb2, ← Matrix.mul_assoc, ha2, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp [map_mul, mul_inv, Units.val_mul, mul_comm]))
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb3 z hz, ha3 z hz]
end GlobalTheory.IdTorus
