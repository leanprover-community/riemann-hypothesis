module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.FieldTheory.Finiteness

@[expose] public section

namespace UpperTheory.Gal.Gen

theorem fixVec_pf : FixVec := by
  intro l _ H _ hH V _ _ _ ρ U hU hne
  classical
  let act : H → (V ⧸ U) →ₗ[ZMod l] (V ⧸ U) :=
    fun h => U.mapQ U (ρ h) (fun u hu => hU h u hu)
  have act_mk : ∀ (h : H) (v : V), act h (U.mkQ v) = U.mkQ (ρ h v) := fun h v => rfl
  letI : MulAction H (V ⧸ U) :=
    { smul := fun h x => act h x
      one_smul := by
        intro x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act 1 (U.mkQ v) = U.mkQ v
        rw [act_mk]
        simp
      mul_smul := by
        intro g h x
        obtain ⟨v, rfl⟩ := U.mkQ_surjective x
        change act (g * h) (U.mkQ v) = act g (act h (U.mkQ v))
        rw [act_mk, act_mk, act_mk]
        simp }
  have smul_def : ∀ (h : H) (x : V ⧸ U), h • x = act h x := fun h x => rfl
  haveI : Nontrivial (V ⧸ U) := Submodule.Quotient.nontrivial_iff.2 hne
  haveI : Finite (V ⧸ U) := Finite.of_surjective U.mkQ U.mkQ_surjective
  have hcard : l ∣ Nat.card (V ⧸ U) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod]
    exact dvd_pow_self l Module.finrank_pos.ne'
  have h0 : (0 : V ⧸ U) ∈ MulAction.fixedPoints H (V ⧸ U) := by
    intro h
    rw [smul_def, map_zero]
  obtain ⟨x, hx, hx0⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point (V ⧸ U) hcard h0
  obtain ⟨v, rfl⟩ := U.mkQ_surjective x
  refine ⟨v, ?_, ?_⟩
  · intro hv
    apply hx0
    rw [eq_comm]
    simpa using hv
  · intro h
    have hfix := hx h
    rw [smul_def, act_mk] at hfix
    exact (Submodule.Quotient.eq U).1 hfix

end UpperTheory.Gal.Gen
