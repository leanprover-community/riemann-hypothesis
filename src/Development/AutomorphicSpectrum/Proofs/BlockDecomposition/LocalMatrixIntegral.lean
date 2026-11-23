module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.BasisSet
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Gunr

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

theorem inclR_mem_Rv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {d : ℕ}
    (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (e : E)
    (h : ∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) :
    inclR (F := F) (Fv F v) e ∈ Rv bs v := by
  simp only [Rv, Set.mem_ofPred_eq]
  intro k
  rw [show inclR (F := F) (Fv F v) e = (1 : Fv F v) ⊗ₜ[F] e from rfl,
    Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
  exact h k

theorem sigR_inclR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (e : E) :
    sigR (Fv F v) σ (inclR (F := F) (Fv F v) e) = inclR (F := F) (Fv F v) (σ e) := by
  show Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ ((1 : Fv F v) ⊗ₜ[F] e)
    = (1 : Fv F v) ⊗ₜ[F] σ e
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem coe_det_matS {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} (S : Subring (Fv F v ⊗[F] E)) {m : ℕ} (X : Matrix (Fin m) (Fin m) E)
    (hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S) :
    (((matS S X hX).det : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) X.det := by
  have h1 : S.subtype.mapMatrix (matS S X hX) = (inclR (F := F) (Fv F v)).mapMatrix X := by
    ext i j
    rfl
  rw [show (((matS S X hX).det : S) : Fv F v ⊗[F] E) = S.subtype (matS S X hX).det from rfl,
    RingHom.map_det, h1, ← RingHom.map_det]

theorem locMat : LocMat := by
  unfold LocMat
  intro F E _ _ _ _ _ σ d bs v S σS hS hσS m X hherm hdet hint
  have memS : ∀ e : E, (∀ k, algebraMap F (Fv F v) (bs.repr e k) ∈ v.adicCompletionIntegers F) →
      inclR (F := F) (Fv F v) e ∈ S := by
    intro e he
    have h := inclR_mem_Rv bs v e he
    rw [← hS] at h
    exact h
  have hX : ∀ i j, inclR (F := F) (Fv F v) (X i j) ∈ S := by
    intro i j
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inl ⟨(i, j, k), rfl⟩
  have hinv : inclR (F := F) (Fv F v) X.det⁻¹ ∈ S := by
    apply memS
    intro k
    apply hint
    simp only [matSet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    exact Or.inr ⟨k, rfl⟩
  refine ⟨hX, ?_, ?_⟩
  · ext i j
    show ((σS (matS S X hX j i) : S) : Fv F v ⊗[F] E) = inclR (F := F) (Fv F v) (X i j)
    rw [hσS]
    show sigR (Fv F v) σ (inclR (F := F) (Fv F v) (X j i)) = inclR (F := F) (Fv F v) (X i j)
    rw [sigR_inclR, hherm]
  · refine isUnit_iff_exists_inv.mpr ⟨⟨inclR (F := F) (Fv F v) X.det⁻¹, hinv⟩, ?_⟩
    apply Subtype.ext
    show (((matS S X hX).det : S) : Fv F v ⊗[F] E) * inclR (F := F) (Fv F v) X.det⁻¹ = 1
    rw [coe_det_matS, ← map_mul, mul_inv_cancel₀ hdet, map_one]

end GlobalTheory.CompanionTheory.Gunr

end
