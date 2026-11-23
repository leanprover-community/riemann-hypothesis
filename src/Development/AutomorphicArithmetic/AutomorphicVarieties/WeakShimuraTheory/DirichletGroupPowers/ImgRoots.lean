module

public import Mathlib.NumberTheory.DirichletCharacter.Basic
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
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.NumberTheory.SelbergSieve
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
import Formalism.ConjugateSelfDual.Statement
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
public import Mathlib.RingTheory.RootsOfUnity.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.large₂.imgRoots :
    ∀ {O : Type} [CommRing O] [IsDomain O] (N : ℕ) [NeZero N] (χ : DirichletCharacter O N) (x : Oˣ), x ^ orderOf χ = 1 → ∃ b : (ZMod N)ˣ, χ.toUnitHom b = x := by
  intro O _ _ N _ χ x hx
  have hn : 0 < orderOf χ := orderOf_pos χ
  haveI : NeZero (orderOf χ) := ⟨hn.ne'⟩
  haveI : Finite χ.toUnitHom.range :=
    Finite.of_surjective χ.toUnitHom.rangeRestrict χ.toUnitHom.rangeRestrict_surjective
  have hle : χ.toUnitHom.range ≤ rootsOfUnity (orderOf χ) O := by
    rintro _ ⟨b, rfl⟩
    rw [mem_rootsOfUnity]
    ext
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply' χ hn.ne', pow_orderOf_eq_one,
      MulChar.one_apply_coe, Units.val_one]
  have hcard : orderOf χ ≤ Nat.card χ.toUnitHom.range := by
    have hpos : 0 < Nat.card χ.toUnitHom.range := Nat.card_pos
    apply orderOf_le_of_pow_eq_one hpos
    refine MulChar.ext fun a => ?_
    rw [MulChar.pow_apply' χ hpos.ne', MulChar.one_apply_coe]
    have h1 := pow_card_eq_one' (G := χ.toUnitHom.range) (x := ⟨χ.toUnitHom a, a, rfl⟩)
    have h2 := congrArg (fun u : χ.toUnitHom.range => ((u : Oˣ) : O)) h1
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
      Units.val_one] at h2
    rw [← MulChar.coe_toUnitHom]
    exact h2
  have heq : χ.toUnitHom.range = rootsOfUnity (orderOf χ) O :=
    Subgroup.eq_of_le_of_card_ge hle ((card_rootsOfUnity O (orderOf χ)).trans hcard)
  have hxmem : x ∈ rootsOfUnity (orderOf χ) O := (mem_rootsOfUnity _ _).2 hx
  rw [← heq] at hxmem
  obtain ⟨b, hb⟩ := hxmem
  exact ⟨b, hb⟩
