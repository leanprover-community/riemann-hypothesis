module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.DepthZeroGoodLines
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses ValuativeRel
open scoped TensorProduct

namespace GlobalTheory.TypeDim

section Finite

variable {F : Type} [Field F] {N : ℕ} {V V' W W' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V']
  [Module ℂ V'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

end Finite

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev part (r t : ℕ) := two (stdSum (rfl : r + t = r + t))

variable {σ : Representation ℂ (GL (Fin r) k) V} {χW χV : kˣ →* ℂˣ}

def diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : GL (Fin (r + t)) 𝒪[k] :=
  emb₂ 𝒪[k] (stdSum (rfl : r + t = r + t)) (a, d)

theorem diagO_ul (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin r) :
    (diagO a d).val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_lr (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i j : Fin t) :
    (diagO a d).val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ll (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin t) (j : Fin r) :
    (diagO a d).val (Fin.natAdd r i) (Fin.castAdd t j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem diagO_ur (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) (i : Fin r) (j : Fin t) :
    (diagO a d).val (Fin.castAdd t i) (Fin.natAdd r j) = 0 := by
  simp [diagO, val_emb₂, stdSum, Matrix.reindex_apply]

theorem hasBlocks_diagO (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : HasBlocks (diagO a d) a d := by
  refine ⟨diagO_ul a d, diagO_lr a d, fun i j => ?_⟩
  rw [diagO_ll]
  exact Ideal.zero_mem _

theorem incl_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (incl k n a).val i j = (a.val i j : k) := rfl

theorem red_val {n : ℕ} (a : GL (Fin n) 𝒪[k]) (i j : Fin n) :
    (red k n a).val i j = IsLocalRing.residue 𝒪[k] (a.val i j) := rfl

theorem incl_diagO_one (a : GL (Fin r) 𝒪[k]) : incl k (r + t) (diagO a 1) = diagOne k r t a := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [incl_val]
  simp only [diagO, diagOne, MonoidHom.comp_apply, MonoidHom.inl_apply, val_emb₂, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  generalize (stdSum (rfl : r + t = r + t)).symm i = x
  generalize (stdSum (rfl : r + t = r + t)).symm j = y
  rcases x with x | x <;> rcases y with y | y <;> simp [incl_val, Matrix.one_apply, apply_ite]

def Nice (r t : ℕ) (w : Equiv.Perm (Fin (r + t))) (S : Finset (Fin r)) : Prop :=
  (∀ i, i ∉ S → w (Fin.castAdd t i) = Fin.castAdd t i) ∧
  (∀ i ∈ S, r ≤ (w (Fin.castAdd t i) : ℕ) ∧ r ≤ (w.symm (Fin.castAdd t i) : ℕ)) ∧ (S = ∅ → w = 1)

end Local

end GlobalTheory.TypeDim
