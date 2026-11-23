module

import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MultiProdCompCongr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTwoBlocksEmptyProductLeftStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdReorder



namespace PositivityTheory.Groth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace GrothendieckAssociativity

theorem class_congr_equiv {N : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin N) k) V} {τ : Representation ℂ (GL (Fin N) k) W}
    (φ : Nonempty (π.Equiv τ)) : cl0 π = cl0 τ := by
  obtain ⟨φ⟩ := φ
  unfold cl0
  by_cases h : HasFiniteLength π
  · rw [dif_pos h, dif_pos (h.of_equiv φ)]
    exact clsGL_congr φ _ _
  · rw [dite_eq_right h, dite_eq_right (fun h' => h (h'.of_equiv φ.symm))]

theorem class_induced_cast {r t N : ℕ} (h : r + t = N) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (GL (Fin r) k × GL (Fin t) k) W) :
    cl0 (ind₂ (stdSum h) ρ) = cl0 (ind₂ (stdSum (rfl : r + t = r + t)) ρ) := by
  subst h
  rfl

theorem class_of_chosen_rep (x : IrrGL (k := k)) : cl0 (IrrGL.rep x) = sg x := by
  exact (dif_pos x.2.rep.hasFiniteLength).trans ((clsGL_irr x.2.rep x.2.rep.hasFiniteLength).trans
    (congrArg (fun c => Finsupp.single (⟨x.1, c⟩ : IrrGL (k := k)) (1 : ℤ)) x.2.cl_rep))

theorem mulR_sg (x y : IrrGL (k := k)) : mulR (sg x) (sg y) = cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep y)) := by
  have h1 := Finsupp.sum_single_index (a := x) (b := (1 : ℤ)) (h := fun z m => (sg y).sum fun w n => (m * n) • cl0 (prod₂ (IrrGL.rep z) (IrrGL.rep w))) (by simp only [Finsupp.sum, zero_mul, zero_smul, Finset.sum_const_zero])
  have h2 := Finsupp.sum_single_index (a := y) (b := (1 : ℤ)) (h := fun w n => ((1 : ℤ) * n) • cl0 (prod₂ (IrrGL.rep x) (IrrGL.rep w))) (by simp only [mul_zero, zero_smul])
  exact h1.trans (h2.trans (by simp only [mul_one, one_smul]))

theorem assoc_gen (h : MulCls k) {r s t : ℕ} {V₁ V₂ V₃ U U' : Type} [AddCommGroup V₁] [Module ℂ V₁]
    [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup V₃] [Module ℂ V₃] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U']
    (π₁ : Representation ℂ (GL (Fin r) k) V₁) (π₂ : Representation ℂ (GL (Fin s) k) V₂)
    (π₃ : Representation ℂ (GL (Fin t) k) V₃) (P : Representation ℂ (GL (Fin (r + s)) k) U)
    (R : Representation ℂ (GL (Fin (s + t)) k) U') (φ : Nonempty (P.Equiv (prod₂ π₁ π₂)))
    (ψ : Nonempty (R.Equiv (prod₂ π₂ π₃))) (s₁ : IsSmooth π₁) (s₂ : IsSmooth π₂) (s₃ : IsSmooth π₃)
    (sP : IsSmooth P) (sR : IsSmooth R) (f₁ : HasFiniteLength π₁) (f₃ : HasFiniteLength π₃)
    (fP : HasFiniteLength P) (fR : HasFiniteLength R) :
    mulR (cl0 P) (cl0 π₃) = mulR (cl0 π₁) (cl0 R) := by
  obtain ⟨a⟩ := ind₂_congr (k := k) (rfl : r + s + t = r + s + t) φ (eqv_refl π₃)
  obtain ⟨b⟩ := ind₂_assoc' (k := k) (rfl : r + s = r + s) (rfl : r + s + t = r + s + t) (rfl : s + t = s + t)
    (Nat.add_assoc r s t).symm π₁ π₂ π₃ s₁ s₂ s₃
  obtain ⟨c⟩ := ind₂_congr (k := k) (Nat.add_assoc r s t).symm (eqv_refl π₁) (eqv_symm ψ)
  have e1 : mulR (cl0 P) (cl0 π₃) = cl0 (prod₂ P π₃) := (h _ _ _ _ P π₃ fP f₃ sP s₃).2.symm
  have e2 : cl0 (prod₂ P π₃) = cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) :=
    class_congr_equiv ⟨(a.trans b).trans c⟩
  have e3 : cl0 (ind₂ (stdSum (Nat.add_assoc r s t).symm) (extTensor π₁ R)) = cl0 (prod₂ π₁ R) :=
    class_induced_cast (Nat.add_assoc r s t).symm (extTensor π₁ R)
  have e4 : cl0 (prod₂ π₁ R) = mulR (cl0 π₁) (cl0 R) := (h _ _ _ _ π₁ R f₁ fR s₁ sR).2
  exact e1.trans (e2.trans (e3.trans e4))

end GrothendieckAssociativity

open GrothendieckAssociativity

variable (k)

theorem assoc (h : MulCls k) : Assoc k := by
  apply CompanionTheory.Groth.assoc <;> assumption

theorem one : One k := by
  apply CompanionTheory.Groth.one <;> assumption

end PositivityTheory.Groth
