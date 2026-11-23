module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorNonscalarOffdiagStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CellFunctorScalarDiagonalStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationUniqueSubquotientStatement
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem proportional_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ')
    (h : ∀ φ ψ : τ'.IntertwiningMap σ, φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap)
    (φ ψ : τ.IntertwiningMap σ) :
    φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap := by
  rcases h (φ.comp E.symm.toIntertwiningMap) (ψ.comp E.symm.toIntertwiningMap) with h0 | ⟨c, hc⟩
  · left
    ext v
    have := LinearMap.congr_fun h0 (E v)
    simpa using this
  · right
    refine ⟨c, ?_⟩
    ext v
    have := LinearMap.congr_fun hc (E v)
    simpa using this

theorem eq_zero_of_equiv {G V V' W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    {τ : Representation ℂ G V} {τ' : Representation ℂ G V'} {σ : Representation ℂ G W}
    (E : τ.Equiv τ') (h : ∀ φ : τ'.IntertwiningMap σ, φ.toLinearMap = 0)
    (φ : τ.IntertwiningMap σ) : φ.toLinearMap = 0 := by
  ext v
  have := LinearMap.congr_fun (h (φ.comp E.symm.toIntertwiningMap)) (E v)
  simpa using this

theorem exists_diagonal_sizeMatrix (a b : ℕ) :
    ∃ D : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)),
      ∀ B : SizeMatrix (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b)), B = D ↔ B.1 false true = 0 := by
  have card_f : Fintype.card (Two (Fin a) (Fin b) false) = a := Fintype.card_fin a
  have card_t : Fintype.card (Two (Fin a) (Fin b) true) = b := Fintype.card_fin b
  refine ⟨⟨fun i j => if i = j then (if i then b else a) else 0, ?_, ?_⟩, fun B => ⟨?_, ?_⟩⟩
  · intro i; cases i <;> simp [card_f, card_t]
  · intro j; cases j <;> simp [card_f, card_t]
  · rintro rfl; simp
  · intro hB
    have r0 := B.2.1 false
    have r1 := B.2.1 true
    have c0 := B.2.2 false
    have c1 := B.2.2 true
    simp only [Fintype.sum_bool, card_f, card_t] at r0 r1 c0 c1
    apply Subtype.ext
    funext i j
    cases i <;> cases j <;> simp <;> omega



theorem mackey_maps_proportional : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), JacquetOfInducedFiltration k → IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ → IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) → (∀ φ ψ : (jac (two (stdSum (rfl : a + b = a + b))) (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))).IntertwiningMap (((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)), φ.toLinearMap = 0 ∨ ∃ c : ℂ, ψ.toLinearMap = c • φ.toLinearMap) := by
  intro k _ _ _ _ a b χ₁ χ₂ hJ h₁ h₂ u₁ u₂ hne
  have hc : Continuous (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom :=
    continuous_prodMk.2 ⟨continuous_apply _, continuous_apply _⟩
  have hsm : IsSmooth ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp
      (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) :=
    isSmooth_comp (isSmooth_extTensor ((isSmooth_ofChar_iff _).2 h₁.detChar)
      ((isSmooth_ofChar_iff _).2 h₂.detChar)) _ hc
  obtain ⟨N, bb, hb⟩ := hJ Bool Bool (Fin (a + b)) (Two (Fin a) (Fin b)) (Two (Fin a) (Fin b))
    (two (stdSum (rfl : a + b = a + b))) (two (stdSum (rfl : a + b = a + b)))
  obtain ⟨S, hm, hbot, htop, hE⟩ := hb (TensorProduct ℂ ℂ ℂ) _ hsm
  obtain ⟨D, hD⟩ := exists_diagonal_sizeMatrix a b
  obtain ⟨t₀, ht₀⟩ := bb.surjective D
  refine GlobalTheory.T.filtration_unique_subquotient _ ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom) N S hm hbot htop t₀ ?_ ?_
  · exact proportional_of_equiv (hE t₀ (SizeMatrix.nonempty_rows (bb t₀)).some (SizeMatrix.nonempty_cols (bb t₀)).some).some
      (GlobalTheory.T.cell_functor_scalar_diagonal k a b χ₁ χ₂ (bb t₀) _ _ ((hD _).1 ht₀))
  · intro t ht
    exact eq_zero_of_equiv (hE t (SizeMatrix.nonempty_rows (bb t)).some (SizeMatrix.nonempty_cols (bb t)).some).some
      (GlobalTheory.T.cell_functor_nonscalar_offdiag k a b χ₁ χ₂ h₁ h₂ u₁ u₂ hne (bb t) _ _ fun h0 =>
        ht (bb.injective (((hD _).2 h0).trans ht₀.symm)))

end GlobalTheory.CompanionTheory.SmGL.Bernstein
