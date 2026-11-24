module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

theorem norm_theta {F : Type} [Field F] [NumberField F] (hF : IsTotallyReal F) (θ : ℝ →+* Ainf F)
    (ε : ℝ) (w : InfinitePlace F) : ‖θ ε w‖ = |ε| := by
  have hw : w.IsReal := hF.isReal w
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  let ρ : ℝ →+* ℝ := (e : w.Completion →+* ℝ).comp ((Pi.evalRingHom _ w).comp θ)
  have hρ : ρ ε = ε := by
    have : ρ = RingHom.id ℝ := Subsingleton.elim _ _
    rw [this]; rfl
  have hnorm : ‖θ ε w‖ = ‖e (θ ε w)‖ := by
    rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) _).symm
  rw [hnorm]
  change ‖ρ ε‖ = |ε|
  rw [hρ, Real.norm_eq_abs]

theorem norm_md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F,
    Continuous θ → ∀ r, IsRay θ r → (∀ (ε : ℝ) (w : InfinitePlace F), ‖θ ε w‖ = |ε|) ∧
      ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ _ r hr
  refine ⟨norm_theta hF θ, fun δ hδ => ?_⟩
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hmd : md (r δ) = (∏ w : InfinitePlace F, ‖(r δ : AF F).1 w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ := IdeleGroup.ideleModule_eq _
  have hfin : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(r δ : AF F).2 v‖ = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    rw [h2]
    exact norm_one
  rw [hmd, hfin, mul_one, h1]
  simp only [norm_theta hF θ δ, abs_of_pos hδ]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay

end
