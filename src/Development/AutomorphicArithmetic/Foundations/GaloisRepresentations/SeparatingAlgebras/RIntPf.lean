module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rInt_pf :
    UpperTheory.Gal.Gen.InjAE → UpperTheory.Gal.Gen.RDens → UpperTheory.Gal.Gen.HalfInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.RInt := by
  intro h1 h2 h3 h4 n t ht0 ht1 l hl
  obtain ⟨hh, -, hev, hnorm⟩ := h4 n t ht0 ht1
  have hpt : ∀ (θ : Fin n → UnitAddCircle) (σ : Equiv.Perm (Fin n)), pt θ ∘ ⇑σ = pt (θ ∘ ⇑σ) :=
    fun _ _ => rfl
  set F : (Fin n → UnitAddCircle) → ℂ := fun θ => monomialChar l (pt θ) * half (t : ℂ) (pt θ) with hF
  have hmc : Continuous fun θ : Fin n → UnitAddCircle => monomialChar l (pt θ) := by
    have := hev (AddMonoidAlgebra.single l 1)
    simpa [evalAt_single] using this
  have hFc : Continuous F := hmc.mul hh
  have hperm : ∀ σ : Equiv.Perm (Fin n),
      ∫ θ : Fin n → UnitAddCircle, F (θ ∘ ⇑σ) = ∫ θ : Fin n → UnitAddCircle, F θ := by
    intro σ
    have hmp := volume_measurePreserving_piCongrLeft (fun _ : Fin n => UnitAddCircle) σ.symm
    rw [← hmp.integral_comp' F]
    congr 1
    funext θ
    congr 1
    funext j
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
  have hae : (fun θ : Fin n → UnitAddCircle => evalAt (pt θ) (hlR (t : ℂ) l) * dens (t : ℂ) (pt θ)) =ᵐ[volume]
      fun θ => ∑ σ : Equiv.Perm (Fin n), F (θ ∘ ⇑σ) := by
    filter_upwards [h1 n] with θ hθ
    rw [h2 n t ht0 ht1 l (pt θ) hθ (hnorm θ)]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hpt]
  rw [integral_congr_ae hae, integral_finsetSum]
  · simp_rw [hperm]
    rw [hF, h3 n t ht0 ht1 l hl, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
    split_ifs <;> simp
  · intro σ _
    have hc : Continuous fun θ : Fin n → UnitAddCircle => θ ∘ ⇑σ :=
      continuous_pi fun i => continuous_apply (σ i)
    exact (hFc.comp hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
