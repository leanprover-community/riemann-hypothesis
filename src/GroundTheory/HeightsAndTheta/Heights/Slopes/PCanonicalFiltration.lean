module

public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: GroundTheory.HeightsAndTheta.Heights.Slopes, GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.Slopes =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.Slopes", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes\npublic import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight\npublic import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import GroundTheory.HeightsAndTheta.Heights.ArithDegree\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace HermitianBundle

variable {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K)

def relSlope (F G : Submodule (𝓞 K) E.carrier) : ℝ :=
  (E.normDegree G - E.normDegree F) / ((E.rank G : ℝ) - E.rank F)

def Semistable : Prop :=
  0 < Module.finrank (𝓞 K) E.carrier ∧
    ∀ F : Submodule (𝓞 K) E.carrier, F ≠ ⊥ → E.slope F ≤ E.slope ⊤

structure IsCanonicalFiltration {m : ℕ} (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier) : Prop where
  bot : f 0 = ⊥
  top : f (Fin.last m) = ⊤
  strictMono : StrictMono f
  saturated : ∀ i, E.Saturated (f i)
  semistable : ∀ (i : Fin m) (G : Submodule (𝓞 K) E.carrier), f i.castSucc < G → G ≤ f i.succ →
    E.relSlope (f i.castSucc) G ≤ E.relSlope (f i.castSucc) (f i.succ)
  anti : StrictAnti fun i : Fin m ↦ E.relSlope (f i.castSucc) (f i.succ)

end HermitianBundle

def trivialFlag {K : Type*} [Field K] [NumberField K] (E : HermitianBundle K) :
    Fin 2 → Submodule (𝓞 K) E.carrier :=
  ![⊥, ⊤]

end

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.Slopes =====

-- ===== clump member: GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration =====
-- clump-header: {"m": "GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration", "h": "module\n\npublic import GroundTheory.HeightsAndTheta.Heights.Slopes\nimport GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Dimension.Torsion.Finite\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

namespace CanonicalFiltration

variable {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)

def saturation (G : Submodule (𝓞 K) E.carrier) : Submodule (𝓞 K) E.carrier where
  carrier := {x | ∃ a : 𝓞 K, a ≠ 0 ∧ a • x ∈ G}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    have h1 : (a * b) • x = b • (a • x) := by rw [mul_comm, mul_smul]
    have h2 : (a * b) • y = a • (b • y) := by rw [mul_smul]
    rw [smul_add, h1, h2]
    exact G.add_mem (G.smul_mem b hx) (G.smul_mem a hy)
  zero_mem' := ⟨1, one_ne_zero, by rw [smul_zero]; exact G.zero_mem⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]
    exact G.smul_mem c hx

theorem le_saturation (G : Submodule (𝓞 K) E.carrier) : G ≤ saturation E G :=
  fun x hx ↦ ⟨1, one_ne_zero, by rw [one_smul]; exact hx⟩

theorem rank_saturation (G : Submodule (𝓞 K) E.carrier) : E.rank (saturation E G) = E.rank G := by
  set S := saturation E G
  set N : Submodule (𝓞 K) S := G.comap S.subtype
  have hN : Module.finrank (𝓞 K) N = E.rank G :=
    (Submodule.comapSubtypeEquivOfLe (le_saturation E G)).finrank_eq
  have hq := Submodule.finrank_quotient_add_finrank N
  have htor : Module.IsTorsion (𝓞 K) (S ⧸ N) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective N q
    obtain ⟨a, ha, hay⟩ := y.2
    refine ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
    rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hay
  have h0 := Module.finrank_eq_zero_iff_isTorsion.mpr htor
  have hS : Module.finrank (𝓞 K) S = E.rank S := rfl
  omega

theorem degree_le_of_le_of_rank_eq {G S : Submodule (𝓞 K) E.carrier} (hGS : G ≤ S)
    (hr : E.rank G = E.rank S) : E.degree G ≤ E.degree S := by
  obtain ⟨s, hs⟩ := E.exists_linearIndependent_rank G
  let t : Fin (E.rank G) → S := fun i ↦ Submodule.inclusion hGS (s i)
  have ht : LinearIndependent (𝓞 K) t :=
    hs.map' _ (LinearMap.ker_eq_bot.mpr (Submodule.inclusion_injective hGS))
  rw [E.degree_eq_of_linearIndependent G hs (Fintype.card_fin _),
    E.degree_eq_of_linearIndependent S ht (by rw [Fintype.card_fin]; exact hr)]
  refine sub_le_sub_right ?_ _
  have hspan : Submodule.span (𝓞 K) (Set.range t) =
      (Submodule.span (𝓞 K) (Set.range s)).map (Submodule.inclusion hGS) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hle : Submodule.span (𝓞 K) (Set.range s) ≤
      (Submodule.span (𝓞 K) (Set.range t)).comap (Submodule.inclusion hGS) := by
    rw [hspan]
    exact Submodule.le_comap_map _ _
  let φ := Submodule.mapQ _ _ (Submodule.inclusion hGS) hle
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ m
    rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, hspan] at hm
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨y, hy, hyx⟩ := hm
    rwa [Submodule.inclusion_injective hGS hyx] at hy
  have hfin : Finite (S ⧸ Submodule.span (𝓞 K) (Set.range t)) :=
    finite_quotient_span ht (by rw [Fintype.card_fin]; exact hr)
  have hfin' : Finite (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Finite.of_injective φ hinj
  have hcard := Nat.card_le_card_of_injective φ hinj
  have hpos : 0 < Nat.card (G ⧸ Submodule.span (𝓞 K) (Set.range s)) := Nat.card_pos
  exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

structure IsCanonicalFrom (F : Submodule (𝓞 K) E.carrier) {m : ℕ}
    (f : Fin (m + 1) → Submodule (𝓞 K) E.carrier) : Prop where
  bot : f 0 = F
  top : f (Fin.last m) = ⊤
  strictMono : StrictMono f
  saturated : ∀ i, E.Saturated (f i)
  semistable : ∀ (i : Fin m) (G : Submodule (𝓞 K) E.carrier), f i.castSucc < G → G ≤ f i.succ →
    E.relSlope (f i.castSucc) G ≤ E.relSlope (f i.castSucc) (f i.succ)
  anti : StrictAnti fun i : Fin m ↦ E.relSlope (f i.castSucc) (f i.succ)

end CanonicalFiltration

end

end GroundTheory.Heights₂.Heights
end -- clump:auto
end -- clump:auto
-- ===== end clump member: GroundTheory.HeightsAndTheta.Heights.Slopes.PCanonicalFiltration =====
