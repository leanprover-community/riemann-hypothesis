module

public import Mathlib.Algebra.MvPolynomial.Basic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.XZ :
    Type → ℕ → ℕ → Type :=
    fun (Lt : Type) (N0 N1 : ℕ) ↦ Lt × ℕ × Fin N0 ⊕ Lt × Fin N0 × Fin N1

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj21.PolyXZ :
    Type → ℕ → ℕ → Type :=
    fun (H : Type) (N0 N1 : ℕ) ↦ MvPolynomial (UpperTheory.Reformulated.B.Qj21.XZ (Bool × H) N0 N1) ℤ

noncomputable def UpperTheory.Reformulated.B.Qj21.lfo :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ × Fin N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (c : ℕ × Fin N1) ↦
      ∑ a : Fin N0, MvPolynomial.X (Sum.inl ((Bool.false, t), c.1, a)) * MvPolynomial.X (Sum.inr ((Bool.false, t), a, c.2))

noncomputable def UpperTheory.Reformulated.B.Qj21.tmL :
    {H : Type} → {N0 N1 : ℕ} → H → List (ℕ × Fin N1) → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 → UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (L : List (ℕ × Fin N1)) (h : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ↦
      (List.map (UpperTheory.Reformulated.B.Qj21.lfo t) L).prod * h

noncomputable def UpperTheory.Reformulated.B.Qj21.nzc :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (0 : ℕ) else (1 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.z0c :
    {N1 : ℕ} → List (ℕ × Fin N1) → ℕ :=
    fun {N1 : ℕ} (L : List (ℕ × Fin N1)) ↦
      (List.map (fun (c : ℕ × Fin N1) ↦ if c.1 = (0 : ℕ) then (1 : ℕ) else (0 : ℕ)) L).sum

noncomputable def UpperTheory.Reformulated.B.Qj21.MS :
    {H : Type} → {N0 N1 : ℕ} → H → ℕ → ℕ → Submodule ℤ (UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) :=
    fun {H : Type} {N0 N1 : ℕ} (t : H) (a b : ℕ) ↦
      Submodule.span ℤ
        {Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1 |
          ∃ (L : List (ℕ × Fin N1)),
            Q = UpperTheory.Reformulated.B.Qj21.tmL t L (1 : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1) ∧
              UpperTheory.Reformulated.B.Qj21.nzc L = a ∧ UpperTheory.Reformulated.B.Qj21.z0c L = b}
