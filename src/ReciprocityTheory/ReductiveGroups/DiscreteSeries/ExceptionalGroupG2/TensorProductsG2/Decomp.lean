module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeC
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeD
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompB
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Decomp

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize, ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompC\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CasimirGapAtNoncompactWeight\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_aeval_intertwine {Y Z : Type*} [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z) (h : ∀ y, ψ (A y) = B (ψ y)) (p : ℂ[X])
    (y : Y) : ψ (aeval A p y) = aeval B p (ψ y) := by
  first | exact UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine .. | (apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine <;> first | assumption | infer_instance)

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

theorem dc_ee_fin_stable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}
    {E : Fin n → Fin n → Module.End ℂ D} {V : Submodule ℂ D} {lam : Fin n → ℝ} (dual : Bool)
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v) (hgap : StdGap ε lam) :
    ∃ W : Submodule ℂ (Fin n → D), FiniteDimensional ℂ W ∧ tensSub V ≤ W ∧
      W ≤ tensSub (genSub E V) ∧ ∀ f ∈ W, eeF dual E f ∈ W := by
  classical
  have hKU : IsKUnitary ε E := isKUnitary_of_isInfUnitary hU
  set EE := eeF dual E with hEE
  set S0 : Submodule ℂ (Fin n → D) := tensSub V with hS0
  have hS0fd : FiniteDimensional ℂ S0 := dc_tensSub_fd hV.1
  have hS0k := dc_tens_kStable dual hV.2.1
  have hS0c : ∀ c, ∀ f ∈ S0, tensF dual E c c f ∈ S0 := fun c => hS0k c c rfl
  let p : Fin n → ℂ[X] := fun c => minpoly ℂ ((tensF dual E c c).restrict (hS0c c))
  have hp0 : ∀ c, p c ≠ 0 := fun c => minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)
  have hpS : ∀ c, ∀ f ∈ S0, aeval (tensF dual E c c) (p c) f = 0 := by
    intro c f hf
    have h := dc_aeval_intertwine S0.subtype ((tensF dual E c c).restrict (hS0c c)) (tensF dual E c c)
      (fun y => rfl) (p c) ⟨f, hf⟩
    rw [minpoly.aeval] at h
    simpa using h.symm
  set Λs : Set (Fin n → ℝ) := {μ | ∀ c, (p c).eval (μ c : ℂ) = 0} with hΛs
  have hΛ : Λs.Finite := by
    refine (Set.Finite.pi (t := fun c => {r : ℝ | (p c).eval (r : ℂ) = 0}) fun c => ?_).subset ?_
    · refine ((p c).roots.toFinset.finite_toSet.preimage Complex.ofReal_injective.injOn).subset ?_
      intro r hr
      simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (hp0 c)).mpr hr
    · intro μ hμ c _
      exact hμ c
  choose kf hkf using fun μ => khw_mem_layer hE hU hV hc hgap μ
  let g : (Fin n → ℝ) → ℕ := fun μ => univ.sup fun c => kf (dc_wsh dual μ c)
  obtain ⟨K0, hK0⟩ := (hΛ.image g).bddAbove
  have hKb : ∀ μ ∈ Λs, ∀ c, kf (dc_wsh dual μ c) ≤ K0 := fun μ hμ c =>
    (Finset.le_sup (f := fun c => kf (dc_wsh dual μ c)) (mem_univ c)).trans (hK0 ⟨μ, hμ, rfl⟩)
  set L := layer ε E V K0 with hL
  have hLfd : FiniteDimensional ℂ L := finiteDimensional_layer hV.1 K0
  have hLk : IsKStableSub ε E L := layer_kStable hE hV.2.1 K0
  have hLM : tensSub (n := n) L ≤ tensSub (genSub E V) := dc_tensSub_mono (layer_le_genSub K0)
  have hpowM : ∀ j, ∀ f ∈ tensSub (genSub E V), (EE ^ j) f ∈ tensSub (genSub E V) := by
    intro j
    induction j with
    | zero => intro f hf; simpa using hf
    | succ j ih => intro f hf; rw [pow_succ', Module.End.mul_apply]; exact dc_eeF_mem dual _ (ih f hf)
  haveI hLfd' : FiniteDimensional ℂ (tensSub (n := n) L) := dc_tensSub_fd hLfd
  have hVg : V ≤ genSub E V := by unfold genSub; exact le_sInf fun T hT => hT.1
  have key : ∀ j, S0.map (EE ^ j) ≤ tensSub L := by
    intro j x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact dc_layer_map dual hE hKU hV.1 hV.2.1 L hLfd hLk (layer_le_genSub K0) p hpS
      (fun μ hμ c w hw hhw => layer_mono (hKb μ hμ c) (hkf _ w hw hhw))
      (EE ^ j) (fun a b _ y => (dc_eeF_pow_comm hE dual a b j y).symm)
      (fun y hy => hpowM j y (dc_tensSub_mono hVg hy)) y hy
  let W : Submodule ℂ (Fin n → D) := ⨆ j, S0.map (EE ^ j)
  have hWL : W ≤ tensSub L := iSup_le key
  refine ⟨W, Submodule.finiteDimensional_of_le hWL, ?_, hWL.trans hLM, ?_⟩
  · have : S0.map (EE ^ 0) ≤ W := le_iSup (fun j => S0.map (EE ^ j)) 0
    simpa [pow_zero, Module.End.one_eq_id, Submodule.map_id] using this
  · intro f hf
    induction hf using Submodule.iSup_induction' with
    | mem j x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine le_iSup (fun j => S0.map (EE ^ j)) (j + 1) ⟨y, hy, ?_⟩
      rw [pow_succ', Module.End.mul_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy

end ReciprocityTheory.ChartRestriction.DS.G2

end

noncomputable section

open Polynomial Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ} {ε : Fin n → Bool}

end ReciprocityTheory.ChartRestriction.DS.G2

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeC\npublic import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ModularCharacterEqOneOnExpHermitian\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Algebra.Order.Star.Real\nimport Mathlib.Algebra.Ring.IsFormallyReal\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Closure\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.UnitarizeD\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Decomp\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset MeasureTheory
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open UnitA UnitB

section SlopeTestRemainingChoices

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem mx_mem {M : Submodule ℂ D} (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ)
    (hst : ∀ a b, ∀ f ∈ tensSub M, tensF dual E a b f ∈ tensSub M) {f : Fin n → D} (hf : f ∈ tensSub M) :
    mx (tensF dual E) X f ∈ tensSub M := by
  unfold mx
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (hst a b f hf)

end SlopeTestRemainingChoices

theorem tens_unitarize (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ,
      (∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V), Q g f = star (Q f g)) ∧
      (∀ f ∈ tensSub (genSub E V), f ≠ 0 → 0 < (Q f f).re) ∧
      (∀ a b, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        Q (tensF dual E a b f) g = adjSign ε a b * Q f (tensF dual E b a g)) ∧
      ∀ k ∈ Kset ε, ∀ f ∈ tensSub (genSub E V), ∀ g ∈ tensSub (genSub E V),
        ∀ f' ∈ tensSub (genSub E V), ∀ g' ∈ tensSub (genSub E V),
          (fun c => ((f' c : D) : H)) = kDiag dual σ k (fun c => ((f c : D) : H)) →
          (fun c => ((g' c : D) : H)) = kDiag dual σ k (fun c => ((g c : D) : H)) → Q f' g' = Q f g := by
  classical
  haveI : (Formalism.REAL.muG ε).IsMulRightInvariant := ⟨fun g => Formalism.REAL.indefinite_unitary_unimodular n ε g⟩
  haveI : FiniteDimensional ℂ V := hV.1
  let bV := Module.finBasis ℂ V
  let ys : Fin (Module.finrank ℂ V) → H := fun j => (((bV j : V) : D) : H)
  have hVM : V ≤ genSub E V := le_sInf fun T hT => hT.1
  have hmem : ∀ f : Fin n → D, f ∈ tensSub (genSub E V) → ∀ c, f c ∈ genSub E V := fun f hf c =>
    (Submodule.mem_pi.1 hf) c (Set.mem_univ c)
  have hst : ∀ a b : Fin n, ∀ f ∈ tensSub (n := n) (genSub E V), tensF dual E a b f ∈ tensSub (genSub E V) :=
    tensSub_stable dual
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (tensSub (n := n) (genSub E V))
  let P : (Fin n → D) →ₗ[ℂ] (Fin n → D) :=
    (tensSub (n := n) (genSub E V)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hPm : ∀ f : Fin n → D, P f ∈ tensSub (genSub E V) := fun f => (Submodule.linearProjOfIsCompl _ _ hC f).2
  have hPid : ∀ f ∈ tensSub (n := n) (genSub E V), P f = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hC ⟨f, hf⟩)
  let u : Fin (Module.finrank ℂ V) → Fin n → (Fin n → D) → Formalism.REAL.UJ ε → ℂ :=
    fun j ξ f => cf dual ε σ (ys j) ξ (hvec f)
  have hL : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ j ξ, MemLp (u j ξ f) 2 (Formalism.REAL.muG ε) := fun f hf j ξ =>
    memLp_cf hσ dual _ ξ _ fun c => hW (f c) (hmem f hf c) ((bV j : V) : D) (hVM (bV j).2)
  have hLP : ∀ (f : Fin n → D) j ξ, MemLp (u j ξ (P f)) 2 (Formalism.REAL.muG ε) := fun f => hL _ (hPm f)
  have hu_add : ∀ j ξ f g, u j ξ (f + g) = u j ξ f + u j ξ g := fun j ξ f g => by
    simp only [u, hvec_add, cf_add]
  have hu_smul : ∀ j ξ (a : ℂ) f, u j ξ (a • f) = a • u j ξ f := fun j ξ a f => by
    simp only [u, hvec_smul, cf_smul]
  let Q0 : (Fin n → D) → (Fin n → D) → ℂ := fun f g =>
    ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ (P f)) (u j ξ (P g))
  let Q : (Fin n → D) →ₗ⋆[ℂ] (Fin n → D) →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) Q0
    (fun f f' g => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_left (hLP f j ξ) (hLP f' j ξ) (hLP g j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_left, Finset.mul_sum, smul_eq_mul, starRingEnd_apply])
    (fun f g g' => by
      simp only [Q0, map_add (f := _), hu_add, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ =>
        pr_add_right (hLP f j ξ) (hLP g j ξ) (hLP g' j ξ))
    (fun a f g => by
      simp only [Q0, map_smul, hu_smul, pr_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])
  have hQ : ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q f g = ∑ j, ∑ ξ, pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ g) := by
    intro f hf g hg
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, hPid f hf, hPid g hg]
  have hskew : ∀ X (hX : inG ε X), ∀ f ∈ tensSub (n := n) (genSub E V), ∀ g ∈ tensSub (genSub E V),
      Q (mx (tensF dual E) X f) g = -Q f (mx (tensF dual E) X g) := by
    intro X hX f hf g hg
    have hXf := mx_mem dual X hst hf
    have hXg := mx_mem dual X hst hg
    rw [hQ _ hXf g hg, hQ f hf _ hXg, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    exact skew (continuous_ex hX) (ex_zero hX) (ex_add hX)
      (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _) (continuous_cf hσ dual _ ξ _)
      (continuous_cf hσ dual _ ξ _)
      (hL f hf j ξ) (hL _ hXf j ξ) (hL g hg j ξ) (hL _ hXg j ξ)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ f x t)
      (fun x t => hasDerivAt_cf hσ hD hX dual (ys j) ξ g x t)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro f _ g _
    simp only [Q, LinearMap.mk₂'ₛₗ_apply, Q0, star_sum, pr_star]
  · intro f hf hf0
    rw [hQ f hf f hf]
    have hre : ∀ j ξ, (pr (Formalism.REAL.muG ε) (u j ξ f) (u j ξ f)).re =
        ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := by
      intro j ξ
      rw [(pr_self_re (hL f hf j ξ)).1, Complex.ofReal_re]
    simp only [Complex.re_sum, hre]
    have hnn : ∀ j ξ, 0 ≤ ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) := fun j ξ =>
      integral_nonneg fun x => by positivity
    by_contra hneg
    push_neg at hneg
    have h0 : ∑ j, ∑ ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 :=
      le_antisymm hneg (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ)
    have hz : ∀ j ξ, ∫ x, ‖u j ξ f x‖ ^ 2 ∂(Formalism.REAL.muG ε) = 0 := by
      intro j ξ
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Finset.sum_nonneg fun ξ _ => hnn j ξ).1 h0 j
        (Finset.mem_univ j)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun ξ _ => hnn j ξ).1 h1 ξ (Finset.mem_univ ξ)
    have hz' : ∀ j ξ x, u j ξ f x = 0 := by
      intro j ξ
      have hi := (pr_self_re (hL f hf j ξ)).2
      have hae := (integral_eq_zero_iff_of_nonneg (fun x => by positivity) hi).1 (hz j ξ)
      have hc : Continuous (fun x => ‖u j ξ f x‖ ^ 2) := ((continuous_cf hσ dual _ ξ _).norm).pow 2
      have h2 := (hc.ae_eq_iff_eq (Formalism.REAL.muG ε) continuous_zero).1 hae
      intro x
      have h3 := congrFun h2 x
      simpa using h3
    apply hf0
    refine cf_inj hσ hD dual (hmem f hf) fun y hy ξ x => ?_
    have hy' : ((y : D) : H) = ∑ j, (bV.repr ⟨y, hy⟩ j) • ys j := by
      have h2 := congrArg (fun w : V => ((w : D) : H)) (bV.sum_repr ⟨y, hy⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
      exact h2.symm
    have e : cf dual ε σ ((y : D) : H) ξ (fun c => ((f c : D) : H)) x =
        ∑ j, star (bV.repr ⟨y, hy⟩ j) * u j ξ f x := by
      simp only [u, cf, hvec, hy', sum_inner, inner_smul_left, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [starRingEnd_apply]
      ring
    rw [e]
    exact Finset.sum_eq_zero fun j _ => by rw [hz' j ξ x, mul_zero]
  · intro a b f hf g hg
    obtain ⟨Z, hZ⟩ : ∃ Z, Z = Jm ε * (Matrix.single a b (1 : ℂ))ᴴ * Jm ε := ⟨_, rfl⟩
    have hX1 : inG ε (Matrix.single a b 1 - Z) := by rw [hZ]; exact inG_sub _
    have hX2 : inG ε (Complex.I • (Matrix.single a b 1 + Z)) := by rw [hZ]; exact inG_add _
    have hTab : tensF dual E a b = (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (-(Complex.I / 2)) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, ← mat_decomp, mx_single]
    have hTba : (1 / 2 : ℂ) • mx (tensF dual E) (Matrix.single a b 1 - Z) +
        (Complex.I / 2) • mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) =
        -(adjSign ε a b • tensF dual E b a) := by
      rw [← mx_smul, ← mx_smul, ← mx_add, mat_decomp2, hZ, single_conj, ← neg_smul, mx_smul, mx_single,
        neg_smul]
    have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    have s2 : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [Complex.conj_I, neg_div]
    have e1 : Q (tensF dual E a b f) g =
        (1 / 2 : ℂ) * Q (mx (tensF dual E) (Matrix.single a b 1 - Z) f) g +
        (Complex.I / 2) * Q (mx (tensF dual E) (Complex.I • (Matrix.single a b 1 + Z)) f) g := by
      rw [hTab]
      simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add (f := _), map_smulₛₗ, smul_eq_mul,
        starRingEnd_apply, s1, s2]
    have e2 := congrArg (fun A : Module.End ℂ (Fin n → D) => Q f (A g)) hTba
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, map_add (f := _), map_smul, map_neg,
      smul_eq_mul] at e2
    rw [e1, hskew _ hX1 f hf g hg, hskew _ hX2 f hf g hg]
    linear_combination (-1 : ℂ) * e2
  · intro k hk f hf g hg f' hf' g' hg' hff hgg
    have hkU : k ∈ UJset ε := closure_inUJ_of_mem_Kset hk
    rw [hQ f' hf' g' hg', hQ f hf g hg]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun ξ _ => ?_
    have e : ∀ (h h' : Fin n → D), (fun c => ((h' c : D) : H)) = kDiag dual σ k (fun c => ((h c : D) : H)) →
        u j ξ h' = fun x => u j ξ h (x * toG k hkU) := by
      intro h h' hh
      funext x
      show cf dual ε σ (ys j) ξ (hvec h') x = _
      rw [show hvec h' = kDiag dual σ (Formalism.MainNotions.S.umat (toG k hkU)) (hvec h) from hh]
      exact cf_kDiag hσ dual _ ξ _ (toG k hkU) hk.2 x
    rw [e f f' hff, e g g' hgg, pr_rt]

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize =====

-- ===== clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp =====
-- clump-header: {"m": "ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap\npublic import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompA\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.DecompC\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Unitarize\npublic import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.DecompB\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem dc_ee_nodal (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ, ∀ f ∈ tensSub (genSub E V),
      Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id) f = 0 := by
  classical
  have hE : IsGlRep E := hD.glRep
  have hU : IsInfUnitary ε E := isInfUnitary_of_isDerivedOn hσ hD
  obtain ⟨Q, -, hpos, hadj, -⟩ := tens_unitarize dual hσ hD hgap hV hc hVK hW
  obtain ⟨W, hWfd, hVW, hWM, hWst⟩ := dc_ee_fin_stable dual hE hU hV hc hgap
  have hsym := dc_eeF_Qsymm hE dual (casimir_genSub hE hc) hadj
  obtain ⟨B, hB⟩ := dc_symm_nodal hpos hsym (dc_eeF_mem dual) hWM hWfd hWst
  refine ⟨B, ?_⟩
  let K0 : Submodule ℂ (Fin n → D) :=
    LinearMap.ker (Polynomial.aeval (eeF dual E) (Lagrange.nodal (dc_cplxPts B) id)) ⊓ tensSub (genSub E V)
  have hle : tensSub (genSub E V) ≤ K0 := by
    refine dc_tens_gen_le dual (fun f hf => ⟨hB f (hVW hf), hWM (hVW hf)⟩) ?_
    intro a b f hf
    refine ⟨?_, dc_tens_genSub_stable dual a b f hf.2⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker] at hf ⊢
    rw [← dc_aeval_intertwine (tensF dual E a b) (eeF dual E) (eeF dual E)
      (fun y => dc_eeF_comm hE dual a b y), hf.1, map_zero]
  exact fun f hf => (hle hf).1

theorem ee_decomp (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) :
    ∃ B : Finset ℝ,
      (∀ f ∈ tensSub (genSub E V), ∃ fb : ℝ → (Fin n → D),
        (∀ b, fb b ∈ tensSub (genSub E V) ∧ eeF dual E (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b) ∧
      ∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ) := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  exact ⟨B, dc_lagrange_decomp (dc_eeF_mem dual) hB, dc_lagrange_eig hB⟩

theorem eigenProj_exists (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (z : ℂ) :
    ∃ P : Module.End ℂ (Fin n → D), IsGKEndo dual ε σ E (genSub E V) P ∧
      (∀ f ∈ tensSub (genSub E V), P (P f) = P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E (P f) = z • P f) ∧
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → P f = f) ∧
      ∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → P f = 0 := by
  obtain ⟨B, hB⟩ := dc_ee_nodal dual hσ hD hgap hV hc hVK hW
  refine ⟨dc_lagProj (eeF dual E) B z, ?_, dc_lagProj_props (dc_eeF_mem dual) hB z⟩
  unfold dc_lagProj
  split_ifs
  · exact dc_isGKEndo_aeval (isGKEndo_eeF hσ hD V dual) _
  · exact dc_isGKEndo_zero'

end ReciprocityTheory.ChartRestriction.DS.G2
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Decomp =====
