module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarLocalThetaFactorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryActionSchwartzInfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTrivialAtPlaceProductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecompositionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.SoStable

theorem so_stable : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ γ, ∀ Φ' ∈ G.M'.So B.ψ B.τ₁, om' γ Φ' ∈ G.M'.So B.ψ B.τ₁ := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT γ Φ' hΦ
  unfold Model.So at hΦ ⊢
  induction hΦ using Submodule.span_induction with
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  | mem x hx =>
    obtain ⟨f, φ, hSB, hcof, hloc, rfl⟩ := hx
    obtain ⟨g₁, g₂, hg, hg₁, hg₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ a' G.V'.J B.v₁ γ.1
    obtain ⟨h₁, h₂, hh, hh₁, hh₂⟩ := GlobalTheory.T.unitary_adelic_place_decomposition F E σ (a + a') G.W.J B.v₁ γ.2
    have hγ : γ = (g₁, h₁) * (g₂, h₂) := Prod.ext hg hh
    obtain ⟨f₂, φ₂, hSB₂, hcof₂, hv₂, he₂⟩ :=
      GlobalTheory.T.theta_trivial_at_place_product hP F E σ B a a' G X om om' hT B.v₁ g₂ h₂ hg₂ hh₂ f φ hSB hcof
    obtain ⟨φ', hSB', hne', hacts, he'⟩ :=
      GlobalTheory.T.local_unitary_action_schwartz_inf hP F E σ B a a' G X om om' hT B.v₁ g₁ hg₁ h₁ hh₁ f₂ φ₂ hSB₂ hcof₂
    rw [hγ, map_mul, mul_apply_eq_comp, he₂, he']
    refine Submodule.subset_span ⟨f₂, φ', hSB', ?_, ?_, rfl⟩
    · filter_upwards [hcof₂, (Set.finite_singleton B.v₁).compl_mem_cofinite] with w hw hw'
      rw [hne' w hw', hw]
    · obtain ⟨hφSB, ι, hι, hsupp⟩ := hloc
      refine ⟨hSB' _, ι, hι, fun Y hY => ?_⟩
      obtain ⟨c, P, Q, hPQ⟩ := GlobalTheory.T.linear_bar_local_theta_factor hP F E σ B a a' G X om om' hT B.v₁ B.τ₁ ι hι g₁ hg₁ h₁ hh₁
        (φ₂ B.v₁) (hSB₂ _) (φ' B.v₁) (hSB' _) hacts
      rw [hPQ, hv₂, hsupp, mul_zero]
      rwa [Matrix.rank_mul_eq_left_of_isUnit_det, Matrix.rank_mul_eq_right_of_isUnit_det]
      · exact (Matrix.isUnit_iff_isUnit_det _).mp P.isUnit
      · exact (Matrix.isUnit_iff_isUnit_det _).mp Q.isUnit

end GlobalTheory.SoStable
