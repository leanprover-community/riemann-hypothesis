module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PhiCharacterResidues.ContinuousResLe
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.phiUnr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (K : Link T c' h) (X : Space (T.fr ∅) (inc h)) (n : ℕ), ∀ (A : ValuationSubring Ω) (v : W.Plc (W.Lp T.L)), IsPlaceOver A v → v ∉ K.V.S' → Ine (F := T.L) A ≤ (K.rho X n).ker := by
  intro Ω _ _ _ l _ c D T c' h K X n A v hA hv g hg
  have hS : v ∉ K.s.S := by rw [← K.hV]; exact hv
  have hl : ¬ A.valuation (l : Ω) < 1 := by
    intro hlt
    apply hS
    left
    apply (hA (l : 𝓞 (W.Lp T.L))).1
    simpa using hlt
  obtain ⟨hκ, hr⟩ := K.unr A v hA hS g hg
  have hβ : K.β g = 1 := K.β_t (K.t_unr A hl hg)
  have hmem : resLe T.F_le g ∈ (T.fr ∅).N := by
    refine ⟨A, ?_, ?_, ?_⟩
    · intro p hp
      have hp' : p = l := by simpa using hp
      rw [hp']
      exact hl
    · exact hg
    · have he : resQ T.F (resLe T.F_le g) = resQ T.L g := by
        ext x
        rfl
      rw [he]
      exact hr
  rw [MonoidHom.mem_ker, UpperTheory.V.Ws.Link.rho_apply]
  have hsc : K.sc n g = 1 := by simp [UpperTheory.V.Ws.Link.sc, hκ, hβ]
  rw [hsc, map_one, one_smul]
  exact X.pair.kill _ hmem
