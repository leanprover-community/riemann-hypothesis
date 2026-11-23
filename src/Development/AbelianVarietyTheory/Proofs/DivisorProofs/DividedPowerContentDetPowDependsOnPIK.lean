module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixVariablesDeterminantPowMonomialShape
public import Mathlib.Data.Nat.PadicValNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddValuationNatCastEqPadicValNat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.RefSum
open GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes (IsIntHom IsOrbit FrobOnType embX primeBelow SplitInK InertInK)
open GlobalTheory.IndefiniteRowSideFullHecke.BigBlockCharacters (HasChars)
open GlobalTheory.IndefiniteRowSideFullHecke.FactorDepthInertBounds (boundAll boundInert boundFine)

namespace GlobalTheory.DetPowContent

open GlobalTheory.DetPowShape

noncomputable def intCoeff (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) : ℤ :=
  (detZ i ^ k).coeff α * α.prod fun _ n => ((n.factorial : ℕ) : ℤ)

theorem cast_intCoeff (C : Type) [Field C] (i k : ℕ) (α : (Σ _ : Fin i, Fin i) →₀ ℕ) :
    ((intCoeff i k α : ℤ) : C) = (detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α := by
  rw [intCoeff, detPow_eq_map, MvPolynomial.coeff_map, Int.cast_mul, GlobalTheory.FGDepth.mfact]
  congr 1 <;> simp [Finsupp.prod]

theorem mem_support_iff' (C : Type) [Field C] [CharZero C] (i k : ℕ) (α) :
    α ∈ (detPow C i k).support ↔ α ∈ (detZ i ^ k).support := by
  rw [MvPolynomial.mem_support_iff, MvPolynomial.mem_support_iff, detPow_eq_map,
    MvPolynomial.coeff_map]
  simp

theorem intCoeff_ne_zero (i k : ℕ) (α) (h : α ∈ (detZ i ^ k).support) : intCoeff i k α ≠ 0 := by
  rw [intCoeff]
  refine mul_ne_zero (MvPolynomial.mem_support_iff.1 h) ?_
  rw [Finsupp.prod]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  exact_mod_cast Nat.factorial_ne_zero _

theorem v_intCast (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ)
    (hp : p.Prime) (hv : v (p : C) = 1) (m : ℤ) (hm : m ≠ 0) :
    v (m : C) = (((padicValNat p m.natAbs : ℕ) : ℝ) : WithTop ℝ) := by
  have h := GlobalTheory.addValuation_natCast_eq_padicValNat C v p hp hv m.natAbs (Int.natAbs_ne_zero.2 hm)
  rcases Int.natAbs_eq m with h1 | h1
  · conv_lhs => rw [h1]
    simpa using h
  · conv_lhs => rw [h1, Int.cast_neg, v.map_neg]
    simpa using h

end GlobalTheory.DetPowContent

namespace GlobalTheory


open GlobalTheory.DetPowShape GlobalTheory.DetPowContent in
theorem detPow_content_const : ∀ (p : ℕ), p.Prime → ∀ i k : ℕ, ∃ κ : ℝ, ∀ (C : Type) [Field C]
    [CharZero C] (v : AddValuation C (WithTop ℝ)), v (p : C) = 1 →
      content v (detPow C i k) = (κ : EReal) := by
  intro p hp i k
  set S := (detZ i ^ k).support with hS
  have hne : S.Nonempty := by
    refine ⟨∑ a : Fin i, Finsupp.single ⟨a, a⟩ k, ?_⟩
    rw [← mem_support_iff' ℚ]
    rw [MvPolynomial.mem_support_iff, (detPow_shape ℚ i k).2.2.1]
    exact one_ne_zero
  let f : ((Σ _ : Fin i, Fin i) →₀ ℕ) → ℕ := fun α => padicValNat p (intCoeff i k α).natAbs
  obtain ⟨α0, hα0, hmin⟩ := S.exists_min_image f hne
  refine ⟨(f α0 : ℝ), fun C _ _ v hv => ?_⟩
  have hval : ∀ α ∈ S, GlobalTheory.FGDepth.toE (v ((detPow C i k).coeff α * GlobalTheory.FGDepth.mfact α)) =
      ((f α : ℝ) : EReal) := by
    intro α hα
    rw [← cast_intCoeff, v_intCast C v p hp hv _ (intCoeff_ne_zero i k α hα)]
    rfl
  unfold GlobalTheory.FGDepth.content
  apply le_antisymm
  · refine iInf₂_le_of_le α0 ((mem_support_iff' C i k α0).2 hα0) ?_
    rw [hval α0 hα0]
  · refine le_iInf₂ fun α hα => ?_
    have hα' := (mem_support_iff' C i k α).1 hα
    rw [hval α hα']
    exact_mod_cast hmin α hα'

end GlobalTheory
