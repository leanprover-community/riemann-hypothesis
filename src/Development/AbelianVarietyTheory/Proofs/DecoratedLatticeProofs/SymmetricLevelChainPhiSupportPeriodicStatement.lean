module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnesRepresent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

theorem _root_.GlobalTheory.T.symmetricLevelChain_phi_support_periodic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (j c : ℕ) (H : j + c = s) (x z : Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin c) (XIx (Fin κ) t j ⊕ Fin (c + 1)) k), ((S.T t).Phi j c H x ≠ 0 → IntM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * x * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val)) ∧ (MaxM ((embA (XIx (Fin κ) t (j + 1)) (GlobalTheory.SplitFlip.diagGL fun i : Fin c => S.ϖ ^ (i.val + 1)))⁻¹.val * z * (embA (XIx (Fin κ) t j) (GlobalTheory.SplitFlip.diagGL fun i : Fin (c + 1) => S.ϖ ^ (i.val + 1))).val) → (S.T t).Phi j c H (x + z) = (S.T t).Phi j c H x) := by
  intro k _ _ _ _ s κ S t _ _ j c H x z
  set o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  set o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  set F := typeFrame (k := k) S.ϖ o
  set F' := typeFrame (k := k) S.ϖ o'
  have hPhi : ∀ y, (S.T t).Phi j c H y = (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((F.coords F' y).submatrix (ixSucc _ t j) id) := fun y => rfl
  constructor
  · intro hx i l
    rw [hPhi] at hx
    have := TypeDatum.intM_of_Phi_ne_zero _ _ hx ((ixSucc _ t j).symm (o.symm i)) (o'.symm l)
    simpa [LatFrame.coords, F, F', typeFrame] using this
  · intro hz
    rw [hPhi, hPhi]
    have e : F.coords F' (x + z) = F.coords F' x + F.coords F' z := by
      unfold LatFrame.coords; rw [Matrix.mul_add, Matrix.add_mul]; rfl
    rw [e]
    exact TypeDatum.Phi_add _ (S.tame _) _ (y := (F.coords F' z).submatrix (ixSucc _ t j) id) fun _ _ => hz _ _
