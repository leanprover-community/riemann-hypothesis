module

public import Development.EtaleCohomology.EtaleSheaves.SHSectionPf
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
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.EtAffNbhdPf

theorem EtAffNbhd_of : LateralTheory.E.SHSectionPf.EtAffNbhd := by
  intro A _ V g hg _
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let x : Spec A := ⟨m, hm.isPrime⟩
  obtain ⟨v, hv⟩ := g.surjective x
  let 𝒰 := V.affineCover
  obtain ⟨p, hp⟩ := 𝒰.covers v
  let ι := 𝒰.f (𝒰.idx v)
  have : IsOpenImmersion ι := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx v)))
  have : Etale ι := inferInstance
  have : Etale (ι ≫ g) := inferInstance
  let f : A ⟶ _ := Spec.preimage (ι ≫ g)
  have hfg : Spec.map f = ι ≫ g := Spec.map_preimage _
  refine ⟨_, f, ι, ?_, hfg.symm, p.asIdeal, p.isPrime, ?_⟩
  · have : Etale (Spec.map f) := by have h := ‹Etale (ι ≫ g)›; rw [← hfg] at h; exact h
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp this
  · have h1 : (Spec.map f).base p = x := by
      rw [hfg]
      change g.base (ι.base p) = x
      rw [hp, hv]
    have h2 : ((Spec.map f).base p).asIdeal = p.asIdeal.comap f.hom := rfl
    rw [← h2, h1]
    exact hm

end LateralTheory.E.EtAffNbhdPf
