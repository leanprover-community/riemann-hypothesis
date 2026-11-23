module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsUniqueUnramifiedCocycleFrobeniusValue
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.UnipotentExponentialSurjective
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc UpperTheory.V.Loc

private theorem ul_exp_onto {A : Type} [CommRing A] [Algebra ℚ A] {n : A} (hn : IsNilpotent n) :
    ∃ x, IsNilpotent x ∧ IsNilpotent.exp x = 1 + n :=
  _root_.UpperTheory.Reformulated.B.UnipotentExponentialSurjective.ul_exp_onto hn

private theorem t2Space_finite_padic_module {l : ℕ} [Fact l.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module.Finite ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] : T2Space V := by
  haveI : IsTopologicalAddGroup V := IsModuleTopology.topologicalAddGroup ℚ_[l] V
  let e0 := (Module.finBasis ℚ_[l] V).equivFun
  exact T2Space.of_injective_continuous e0.injective
    (IsModuleTopology.continuous_of_linearMap e0.toLinearMap)

theorem UpperTheory.lift_unramified_unipotent_character :
    ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {B B' : Type} [CommRing B] [CommRing B'] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra ℚ_[l] B'] [Module.Finite ℚ_[l] B'] (p : B →ₐ[ℚ_[l]] B'), Function.Surjective p → (∀ a, p a = 0 → IsNilpotent a) → ∀ u' : GQ v →* B'ˣ, QCont l (fun g => (u' g : B')) → (∀ g ∈ Iq v, u' g = 1) → (∀ g, IsNilpotent ((u' g : B') - 1)) → ∃ u : GQ v →* Bˣ, QCont l (fun g => (u g : B)) ∧ (∀ g ∈ Iq v, u g = 1) ∧ ∀ g, p (u g : B) = (u' g : B') := by
  intro v l _ _ B B' _ _ _ _ _ _ p hp hker u' hc' hI' hn'
  letI : Algebra ℚ B := ((algebraMap ℚ_[l] B).comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : Algebra ℚ B' := ((algebraMap ℚ_[l] B').comp (algebraMap ℚ ℚ_[l])).toAlgebra
  letI : TopologicalSpace B := moduleTopology ℚ_[l] B
  letI : TopologicalSpace B' := moduleTopology ℚ_[l] B'
  haveI : IsModuleTopology ℚ_[l] B := ⟨rfl⟩
  haveI : IsModuleTopology ℚ_[l] B' := ⟨rfl⟩
  haveI : IsTopologicalAddGroup B := IsModuleTopology.topologicalAddGroup ℚ_[l] B
  haveI : IsTopologicalAddGroup B' := IsModuleTopology.topologicalAddGroup ℚ_[l] B'
  haveI : ContinuousSMul ℚ_[l] B := IsModuleTopology.toContinuousSMul ℚ_[l] B
  haveI : ContinuousSMul ℚ_[l] B' := IsModuleTopology.toContinuousSMul ℚ_[l] B'
  haveI : T2Space B' := t2Space_finite_padic_module (l := l)
  obtain ⟨σ, hσ⟩ := (iqBasic v).2.2.2.1
  obtain ⟨x', hx', he'⟩ := ul_exp_onto (hn' σ)
  obtain ⟨x, rfl⟩ := hp x'
  have hx : IsNilpotent x := by
    obtain ⟨k, hk⟩ := hx'
    exact (hker (x ^ k) (by rw [map_pow, hk])).of_pow
  obtain ⟨c, ⟨hc, hcI, hcσ⟩, -⟩ := existsUnique_unramified_cocycle_frobenius_value (l := l) (A := ℚ_[l]) (V := ℚ_[l])
    (1 : Representation ℚ_[l] (GQ v) ℚ_[l]) continuous_snd (fun _ _ => rfl) σ hσ 1
  have hadd : ∀ g h, c (g * h) = c g + c h := fun g h => hc.2 g h
  have hcc : Continuous c := hc.1
  have hc1 : c 1 = 0 := hcI 1 (one_mem _)
  let f : GQ v →* B :=
    { toFun := fun g => IsNilpotent.exp (c g • x)
      map_one' := by rw [hc1, zero_smul, IsNilpotent.exp_zero]
      map_mul' := fun g h => by
        rw [hadd, add_smul, IsNilpotent.exp_add_of_commute (Commute.all _ _) (hx.smul _) (hx.smul _)] }
  have hf : Continuous f := by
    obtain ⟨k, hk⟩ := hx
    have : (f : GQ v → B) = fun g => ∑ i ∈ Finset.range k,
        ((((i.factorial : ℚ)⁻¹ : ℚ) : ℚ_[l]) * c g ^ i) • x ^ i := by
      funext g
      change IsNilpotent.exp (c g • x) = _
      rw [IsNilpotent.exp_eq_sum (k := k) (by rw [smul_pow, hk, smul_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_smul, Rat.cast_smul_eq_qsmul, smul_pow]
    rw [this]
    fun_prop
  have hfI : ∀ g ∈ Iq v, f g = 1 := fun g hg => by
    change IsNilpotent.exp (c g • x) = 1
    rw [hcI g hg, zero_smul, IsNilpotent.exp_zero]
  refine ⟨f.toHomUnits, hf, fun g hg => Units.ext (hfI g hg), fun g => ?_⟩
  let f1 : GQ v →* B' := (p : B →* B').comp f
  let f2 : GQ v →* B' := (Units.coeHom B').comp u'
  have hcl : IsClosed ((f1.eqLocus f2 : Subgroup (GQ v)) : Set (GQ v)) :=
    isClosed_eq ((IsModuleTopology.continuous_of_linearMap p.toLinearMap).comp hf) hc'
  have hle : Iq v ⊔ Subgroup.zpowers σ ≤ f1.eqLocus f2 := by
    refine sup_le (fun k hk => ?_) ((Subgroup.zpowers_le).2 ?_)
    · change p (f k) = (u' k : B')
      rw [hfI k hk, hI' k hk, map_one, Units.val_one]
    · change p (IsNilpotent.exp (c σ • x)) = (u' σ : B')
      rw [hcσ, one_smul, IsNilpotent.map_exp hx, he', add_sub_cancel]
  have := Subgroup.topologicalClosure_minimal _ hle hcl
  rw [frobDense σ hσ] at this
  exact this (Subgroup.mem_top g)
