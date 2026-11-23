module

public import Formalism.LocalToGlobal.Columns.DecoFin
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapFacts
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import Formalism.LocalToGlobal.Columns.TiedGlPl
public import Formalism.LocalToGlobal.Columns.TwQSplit
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapLoc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Formalism.LocalToGlobal.Columns.TiedGlLoc

@[expose] public section

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.UG Formalism.L2.DIV

section SpP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E)
  (P : Pl E) (ϖ : 𝓞 E) (hϖ : ϖ ∈ P.asIdeal) (hcϖ : cO E ϖ ∉ P.asIdeal)
  (s : Formalism.MainNotions.Gaps.LG.SplitAt hc.sig (underPl F P) (ϖ : E))

abbrev qbPhi : E →+* (underPl F P).adicCompletion F :=
  (RingHom.fst _ _).comp (s.φ.toRingHom.comp (inclE (F := F) ((underPl F P).adicCompletion F)))

theorem phi_integral_valuation_le_one (r : 𝓞 E) : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((s.int _).1 (Formalism.MainNotions.Gaps.LG.sc_left_mem _ r)).1

theorem qsp_sp_F (x : F) : qbPhi hc P ϖ s (algebraMap F E x) = algebraMap F ((underPl F P).adicCompletion F) x := by
  show (s.φ (algebraMap F E x ⊗ₜ[F] (1 : (underPl F P).adicCompletion F))).1 = _
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, s.alg]


include hϖ hcϖ in

theorem qsp_sp_P (r : 𝓞 E) : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal := by
  have hval : Valued.v (gloPhi (underPl F P) s.φ (inclE (F := F) ((underPl F P).adicCompletion F) (algebraMap (𝓞 E) E ϖ))) < 1 := s.ori
  have hker := glk_ker hc (underPl F P) s.φ s.alg P (qsp_isOver P) ϖ hcϖ hval
  have key : ∀ a : 𝓞 E, a ∈ P.asIdeal → Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E a)) < 1 := fun a ha => by
    have h1 := hker a ha
    rw [gloRho_oToS] at h1
    have h2 := glk_val_lt (underPl F P) _ h1
    exact h2
  refine ⟨fun h => ?_, key r⟩
  by_contra hr
  obtain ⟨y, i, hi, e⟩ := P.isMaximal.exists_inv hr
  have h1 : qbPhi hc P ϖ s (algebraMap (𝓞 E) E y) * qbPhi hc P ϖ s (algebraMap (𝓞 E) E r) +
      qbPhi hc P ϖ s (algebraMap (𝓞 E) E i) = 1 := by
    rw [← map_mul, ← map_mul, ← map_add (f := _), ← map_add (f := _), e, map_one, map_one]
  have h2 : Valued.v (qbPhi hc P ϖ s (algebraMap (𝓞 E) E y) * qbPhi hc P ϖ s (algebraMap (𝓞 E) E r)) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (phi_integral_valuation_le_one hc P ϖ s y)) h
  have h3 := Valuation.map_add_lt Valued.v h2 (key i hi)
  rw [h1, map_one] at h3
  exact lt_irrefl _ h3

end SpP

end Formalism.L2.Col
