module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelArchimedeanExponent
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

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.FockVac

theorem span_finiteDimensional : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    FiniteDimensional ℂ (Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀}) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  by_cases h : ∃ g : SInf F (Fin n × Fin d), M.IsGauss B.ψ B.emb g ∧ g ≠ 0
  · obtain ⟨g, hg, hg0⟩ := h
    have hle : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} ≤ Submodule.span ℂ {g} := by
      refine Submodule.span_le.2 fun f hf => ?_
      obtain ⟨z, rfl⟩ := GlobalTheory.RealDict.FockMap.gauss_line M B.ψ B.emb hP.base.cm hP.base.std
        (fun w => (hP.herm.cartan w).1) (fun w => (hP.skew.cartan w).1) f g hg hg0 hf
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    exact Submodule.finiteDimensional_of_le hle
  · push_neg at h
    have hb : Submodule.span ℂ {f₀ : SInf F (Fin n × Fin d) | M.IsGauss B.ψ B.emb f₀} = ⊥ :=
      Submodule.span_eq_bot.2 fun f hf => by_contra fun h0 => h0 (h f hf)
    rw [hb]
    infer_instance

end GlobalTheory.FockVac
