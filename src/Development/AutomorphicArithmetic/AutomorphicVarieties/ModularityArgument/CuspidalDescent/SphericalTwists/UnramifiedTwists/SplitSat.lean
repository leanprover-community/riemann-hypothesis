module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne GlobalTheory.LFun GlobalTheory.PRep UpperTheory.V.Af.Gu

private theorem sat_of_equiv {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V W : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {ρ' : Representation ℂ (GL (Fin n) (w.adicCompletion E)) W}
    (e : ρ.Equiv ρ') {B : Multiset ℂˣ} (h : HasSatGL w ρ B) : HasSatGL w ρ' B := by
  have he : ∀ g v, e.toLinearEquiv (ρ g v) = ρ' g (e.toLinearEquiv v) := fun g v =>
    e.toIntertwiningMap.isIntertwining _ _ g v
  constructor
  · obtain ⟨x, hx⟩ := h.exists_vec
    have h1 := hx.map e.toLinearEquiv.toLinearMap he ((map_ne_zero_iff _ e.toLinearEquiv.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective y
    refine (h.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => e.toLinearEquiv.injective ?_) fun hx => h0 (by rw [hx, map_zero])).map
      e.toLinearEquiv.toLinearMap he h0
    rw [he]
    exact GlobalTheory.LGrp.mem_fixed.1 hy k hk
