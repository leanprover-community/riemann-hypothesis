module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.IsAlgClosureField
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuChi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AutomorphicCharacters.AuCont
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




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp
theorem UpperTheory.V.Ws.isAlgChar_pushCh_link_kappa :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D) (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h) (ι : PadicAlgCl l ≃+* ℂ), Af.IsAlgChar ι (W.pushCh (algebraMap c'.O (PadicAlgCl l)) K.κ) := by
  intro hP Ω _ _ _ l _ c D T c' h K ι
  refine (_root_.UpperTheory.V.Af.algOfCyc_s hP T.L Ω l ι).1 _ (auCont c' K.κ K.κ_cont) fun w hw => ?_
  obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w := exists_isPlaceOver Ω w
  have hl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 T.L)).2 hw
    have e : algebraMap T.L Ω (((l : ℕ) : 𝓞 T.L) : T.L) = (l : Ω) := by simp
    rwa [e] at h1
  obtain ⟨a, b, k, hk, -, H⟩ := K.cyc A hl
  refine ⟨A, hA, a, k, hk, fun s hs => ?_⟩
  rw [← (auChi T.L Ω c').1]
  have h2 := congrArg (Units.map (algebraMap c'.O (PadicAlgCl l)).toMonoidHom) (H s hs).1
  rw [map_pow, map_mul, map_zpow, map_one] at h2
  exact h2
end
