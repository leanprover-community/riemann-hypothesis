module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open Matrix

namespace GlobalTheory.MulVecProduct

theorem mulVec_eq_prod_smul {n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Φ : (ι → GL (Fin n) ℂ) → Matrix κ κ ℂ}
    (h1 : Φ (1 : ι → GL (Fin n) ℂ) = (1 : Matrix κ κ ℂ))
    (hmul : ∀ (g h : ι → GL (Fin n) ℂ), Φ (g * h) = Φ g * Φ h)
    {v : κ → ℂ} {lam : ι → Fin n → ℤ}
    (hv : ∀ (τ : ι), GlobalTheory.AlgWtHW.IsBEig (fun (B : GL (Fin n) ℂ) ↦ Φ (Pi.mulSingle τ B)) v (lam τ))
    (g : ι → GL (Fin n) ℂ)
    (hg : ∀ (τ : ι), Matrix.BlockTriangular (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) id) :
    Matrix.mulVec (Φ g) v =
      (∏ τ : ι, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
  classical
  have key : ∀ S : Finset ι, Φ (fun τ => if τ ∈ S then g τ else 1) *ᵥ v =
      (∏ τ ∈ S, ∏ i : Fin n, (↑(g τ) : Matrix (Fin n) (Fin n) ℂ) i i ^ lam τ i) • v := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have h0 : (fun τ : ι => if τ ∈ (∅ : Finset ι) then g τ else 1) = 1 := by
        funext τ
        simp
      rw [h0, h1, Finset.prod_empty, one_smul, Matrix.one_mulVec]
    | insert a S ha ih =>
      have hsplit : (fun τ => if τ ∈ insert a S then g τ else 1) =
          Pi.mulSingle a (g a) * (fun τ => if τ ∈ S then g τ else 1) := by
        funext τ
        by_cases hτ : τ = a
        · subst hτ
          simp [ha]
        · simp [hτ]
      have ha' := (hv a).2 (g a) (hg a)
      simp only at ha'
      rw [hsplit, hmul, ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, ha', smul_smul,
        Finset.prod_insert ha]
      congr 1
      ring
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset ι) then g τ else 1) = g := by
    funext τ
    simp
  have := key Finset.univ
  rw [hall] at this
  exact this

end GlobalTheory.MulVecProduct
