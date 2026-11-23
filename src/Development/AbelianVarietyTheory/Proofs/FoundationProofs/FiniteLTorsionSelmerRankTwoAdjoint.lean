module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutsideStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivCoboundaryOfReducedCocyclesCohomologousStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReducedSelmerCochainMemContinuousCocyclesOfContStatement
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem finite_lTorsion_divSel : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  intro hL l _ Ω _ _ _ S A W c hS hW hO hN
  have hH : Finite (H1 (resRep c W hO S hN)) :=
    (hL.gf ℚ Ω l 1 (ResPlane c) S (resRep c W hO S hN) one_pos hS (GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside l Ω S W c hO hN hW)).2.1
  have key : ∀ x : {x : DivSel c W S A // l • x = 0}, ∃ (z : G ℚ Ω → Fin 2 → Qbar l) (hz : z ∈ divSelCoc c W S A)
      (y : Fin 2 → Qbar l), VecE c y ∧ (∀ s i, (l : Qbar l) * z s i - (mat W s *ᵥ y - y) i ∈ c.O) ∧
      (QuotientAddGroup.mk ⟨z, hz⟩ : DivSel c W S A) = x.1 := by
    rintro ⟨x, hx⟩
    obtain ⟨⟨z, hz⟩, rfl⟩ := QuotientAddGroup.mk_surjective x
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx
    obtain ⟨y, hy, hzy⟩ := hx
    refine ⟨z, hz, y, hy, fun s i => ?_, rfl⟩
    have := hzy s i
    simpa only [AddSubgroup.coe_nsmul, Pi.smul_apply, nsmul_eq_mul] using this
  choose z hz y hy hzy hx using key
  refine Finite.of_injective (fun x => (Submodule.Quotient.mk
    ⟨descS S (resCoc c W (z x) (y x)), GlobalTheory.T.reduced_selmer_cochain_mem_continuous_cocycles_of_cont l Ω S A W c hO hN hW (z x) (hz x) (y x) (hy x) (hzy x)⟩ :
      H1 (resRep c W hO S hN))) ?_
  intro x x' h
  rw [Submodule.Quotient.eq, Submodule.mem_comap, (mem_coboundaries1 _ _)] at h
  obtain ⟨m, hm⟩ := h
  have hd := GlobalTheory.T.divCoboundary_of_reducedCocycles_cohomologous l Ω W c hO (z x) (z x') (y x) (y x') (hy x) (hy x') (hzy x) (hzy x') ⟨m, fun s => by
    have := hm (toGS Ω (S : Set Pl) s)
    simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at this
    rw [descS_resCoc_toGS c W S A hO hN (hz x) (y x) (hzy x) s,
      descS_resCoc_toGS c W S A hO hN (hz x') (y x') (hzy x') s] at this
    rw [this, resRep_toGS]⟩
  apply Subtype.ext
  rw [← hx x, ← hx x', QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : (↑(-(⟨z x, hz x⟩ : divSelCoc c W S A) + ⟨z x', hz x'⟩) : G ℚ Ω → Fin 2 → Qbar l) = -(z x - z x') := by
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
  rw [this]
  exact (divCob c W).neg_mem hd

end GlobalTheory.Ord2

end
