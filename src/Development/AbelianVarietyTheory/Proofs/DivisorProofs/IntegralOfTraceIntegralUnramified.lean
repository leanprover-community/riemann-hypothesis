module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinrankLeOfMapLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU

@[expose] public section

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc
open scoped nonZeroDivisors

namespace GlobalTheory.LieDisc

theorem isIntegral_of_trace_integral :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : E,
      (∀ a : E, IsIntegral ℤ a → IsIntegral ℤ (w * a + cc (w * a))) → IsIntegral ℤ w := by
  intro E _ _ _ hu w hw
  set F := maximalRealSubfield E
  have hfu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E) := by
    haveI : Algebra.Unramified (𝓞 F) (𝓞 E) := hu
    infer_instance
  have hd : differentIdeal (𝓞 F) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hfu
  have h10 : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have h := coeIdeal_differentIdeal (𝓞 F) F (L := E) (B := 𝓞 E)
    rw [hd, FractionalIdeal.coeIdeal_top] at h
    exact (inv_eq_one.1 h.symm)
  have hmem : w ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have ht := Formalism.FourierDecayAlt.P.S6x3.trace_eq E (w * algebraMap (𝓞 E) E b)
    have hi : IsIntegral ℤ (Algebra.trace F E (w * algebraMap (𝓞 E) E b)) := by
      rw [← isIntegral_algebraMap_iff (B := E), ht]
      exact hw _ (RingOfIntegers.isIntegral_coe b)
    exact ⟨⟨_, hi⟩, rfl⟩
  rw [hdual] at hmem
  obtain ⟨z, hz⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
  rw [← hz]
  exact RingOfIntegers.isIntegral_coe z

end GlobalTheory.LieDisc
