module

public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
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

noncomputable section
namespace GlobalTheory.Survey.PiTwistNegation
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

theorem halfI_ne_top (T : Core D) (i : Fin 2) : halfI T i ≠ ⊤ := by
  intro h
  have hc : ((T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))).comap
      (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ := by
    rw [show (T.pb i).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = ⊤ from h, Ideal.comap_top]
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat] at hc
  exact (T.pb i).isPrime.ne_top hc

theorem halfEX_iff_le (T : Core D) (h : LawsM T) (X : ErrX D) :
    HalfEX T X ↔ ∀ i, T.Q.l.Mb ≤ Ideal.span {barE D (X.piG i)} := by
  have hle : ∀ i, T.Q.l.Mb ≤ halfI T i := by
    intro i
    rw [Mb_eq T h]
    fin_cases i
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
  change (∀ i, barE D (X.piG i) ∈ halfI T i) ↔ _
  refine forall_congr' fun i => ⟨fun hb => ?_, fun hM => ?_⟩
  · rw [← (piOf_eq_bar_iff T h X i).2 hb, span_piOf T h]; exact hle i
  · by_contra hb
    have hp : piOf T X i = X.piG i := by
      classical
      unfold piOf; rw [if_neg hb]

    have h1 : T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Ideal.span {barE D (X.piG i)} := by
      rw [← hp, ← bar_core T, span_bar_piOf T h]; exact Ideal.map_mono (hle i)
    have ht : Ideal.span {barE D (X.piG i)} = ⊤ := by
      rw [eq_top_iff, ← T.Q.l.coprime]; exact sup_le hM h1
    have hu : IsUnit (X.piG i) := by
      have := (Ideal.span_singleton_eq_top.1 ht).map (barE D)
      rwa [barE_barE] at this
    apply halfI_ne_top T i
    rw [← span_piOf T h X i, hp, Ideal.span_singleton_eq_top]; exact hu

end GlobalTheory.Survey.PiTwistNegation
