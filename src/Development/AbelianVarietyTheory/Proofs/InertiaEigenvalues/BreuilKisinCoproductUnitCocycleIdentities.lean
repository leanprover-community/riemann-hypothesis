module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Imports
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonMatrixMulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscPeriodComparisonRelationMapPrismHomStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TopBasisDiscRegularStatement
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

namespace GlobalTheory.BSP

theorem height_rel_unit_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (ε : Matrix (Fin d) (Fin d) En.Q.A),
    ht.Rel (BK.hf En.inl X) En.inl En.inr (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) →
    ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B) (ι : Type), TopBasis (BK.hf f₀) bk.J ι →
    (∀ k : Hom En.Q B, k.comp En.inl = k.comp En.inr → ε.map k.f = 1) ∧
    ∀ k₁ k₂ k₃ : Hom En.Q B, k₁.comp En.inr = k₂.comp En.inl → k₁.comp En.inl = k₃.comp En.inl →
      k₂.comp En.inr = k₃.comp En.inr → ε.map k₁.f * ε.map k₂.f = ε.map k₃.f := by
  intro l _ K bk d ρ τ s ht En ε hε B f₀ ι tb
  have H := GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk B.A (BK.hf f₀) ι tb
  have hinj := H.1
  have hE := H.2.1
  have key : ∀ k : Hom En.Q B, ht.Rel (BK.hf f₀ X) (k.comp En.inl) (k.comp En.inr)
      ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
    intro k
    have H2 := GlobalTheory.T.discPeriod_comparison_relation_map_prismHom l K bk d ρ τ s ht En.Q B En.inl En.inl En.inr f₀ k (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)) hε
    refine H2.1.elim fun Fk hFk => ?_
    have h := H2.2
    have e : (ε.map (toDisc l (BK.hf En.inl X) bk.ρ₀)).map Fk =
        (ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀) := Matrix.ext fun i j => hFk.ext (ε i j)
    exact e ▸ h Fk hFk
  have inj : ∀ M N : Matrix (Fin d) (Fin d) B.A, M.map (toDisc l (BK.hf f₀ X) bk.ρ₀) =
      N.map (toDisc l (BK.hf f₀ X) bk.ρ₀) → M = N := fun M N h =>
    Matrix.ext fun i j => hinj (congrFun (congrFun h i) j)
  have tr : ∀ (f f' g g' : Hom bk.prism B) (M : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)),
      f = f' → g = g' → ht.Rel (BK.hf f₀ X) f g M → ht.Rel (BK.hf f₀ X) f' g' M := fun _ _ _ _ _ hf hg h =>
    hf ▸ hg ▸ h
  refine ⟨fun k hk => ?_, fun k₁ k₂ k₃ h₁ h₂ h₃ => ?_⟩
  · have h : ht.Rel (BK.hf f₀ X) (k.comp En.inr) (k.comp En.inr)
        ((ε.map k.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ hk rfl (key k)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ 1 1 _ (ht.rel_one _ _) (ht.rel_one _ _) h
    exact inj _ _ ((e.symm.trans (mul_one 1)).trans (Matrix.map_one _ (map_zero _) (map_one _)).symm)
  · have e1 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inl)
        ((ε.map k₁.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ rfl h₁ (key k₁)
    have e3 : ht.Rel (BK.hf f₀ X) (k₁.comp En.inl) (k₂.comp En.inr)
        ((ε.map k₃.f).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := tr _ _ _ _ _ h₂.symm h₃.symm (key k₃)
    have e := GlobalTheory.T.discPeriod_comparison_matrix_mul l K bk d ρ τ s ht B f₀ hE _ _ _ _ _ _ e1 (key k₂) e3
    exact inj _ _ (Matrix.map_mul.trans e)

end GlobalTheory.BSP
