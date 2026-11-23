module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StProjectionInjectiveOffHypersurface
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StConormalGenerationGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StFrameJacobianGeneric
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameImplicitGraph
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

theorem ProjectionInjectiveOffHypersurface.proof (hF : FrameJacobianGeneric.Statement) :
    ProjectionInjectiveOffHypersurface.Statement := by
  classical
  intro σ _ I k hI hk
  set n := Fintype.card σ
  let e : σ ≃ Fin n := Fintype.equivFin σ
  let φ : MvPolynomial σ ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ := renameEquiv ℂ e
  let J : Ideal (MvPolynomial (Fin n) ℂ) := I.map φ
  have hJ : J.IsPrime := Ideal.map_isPrime_of_equiv φ
  have hJk : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) := by
    rw [← hk]
    exact (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv I J φ rfl).symm)
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, -, hcard, hfJ, -, hdet, -⟩ := hF n k J hJ hJk b

  let T : (σ → ℂ) → EuclideanSpace ℂ (Fin n) := fun x => WithLp.toLp 2 (x ∘ e.symm)
  have hT : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ),
      eval (fun i => T x i) p = eval x (φ.symm p) := by
    intro x p
    have : φ.symm p = rename e.symm p := rfl
    rw [this, eval_rename]
  have hTinj : Function.Injective T := by
    intro x y hxy
    funext s
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v (e s)) hxy
    simpa [T] using this
  have hTc : Continuous T :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _)
  refine ⟨φ.symm (frameJacobianDet b I₀ f), ?_, ?_⟩
  · intro hmem
    apply hdet
    exact (Ideal.mem_map_of_equiv φ _).2 ⟨_, hmem, by simp⟩
  intro z hz hzh
  have hf0 : ∀ x ∈ zeroSetIn I, ∀ j, eval (fun i => T x i) (f j) = 0 := by
    intro x hx j
    obtain ⟨q, hq, hqf⟩ := (Ideal.mem_map_of_equiv φ (f j)).1 (hfJ j)
    rw [hT, ← hqf, AlgEquiv.symm_apply_apply]
    exact hx q hq
  have hz' : eval (fun i => T z i) (frameJacobianDet b I₀ f) ≠ 0 := by rwa [hT]
  obtain ⟨Ω, V, g, -, hV, hzV, -, -, hpg, hgraph⟩ :=
    FrameImplicitGraph.proof n b I₀ f (T z) (hf0 z hz) hz' Set.univ isOpen_univ (Set.mem_univ _)
  let c : Fin k ≃ I₀ := (Fintype.equivFinOfCardEq (by simpa using hcard)).symm
  let A : (σ → ℂ) →L[ℂ] (Fin k → ℂ) :=
    ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (e.symm (c j : Fin n))
  refine ⟨T ⁻¹' V, hV.preimage hTc, hzV, A, ?_⟩

  have hback : ∀ x ∈ zeroSetIn I ∩ T ⁻¹' V, g (frameProj b I₀ (T x)) = T x := by
    rintro x ⟨hx, hxV⟩
    have hmem : T x ∈ {y : EuclideanSpace ℂ (Fin n) | ∀ j, eval (fun i => y i) (f j) = 0} ∩ V :=
      ⟨hf0 x hx, hxV⟩
    rw [hgraph] at hmem
    obtain ⟨w, hw, hwx⟩ := hmem
    rw [← hwx, hpg w hw]
  intro x hx y hy hAxy
  apply hTinj
  have hproj : frameProj b I₀ (T x) = frameProj b I₀ (T y) := by
    funext i
    have := congrFun hAxy (c.symm i)
    show inner ℂ (b i) (T x) = inner ℂ (b i) (T y)
    rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_inner]
    simpa [A, T] using this
  rw [← hback x hx, ← hback y hy, hproj]

theorem ProjectionInjectiveOffHypersurface.proof_of_rank (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : ProjectionInjectiveOffHypersurface.Statement :=
  ProjectionInjectiveOffHypersurface.proof (FrameJacobianGeneric.proof hR hC)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
