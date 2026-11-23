module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.FormsFiniteAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotOfMemAdjoinCommuting
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModQuantumDetLeviBlocksOfParabolic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchExpSingleUnipotentEmbedding
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QdetGeneratesUniversalEnvelopingCentre
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UActionMemUnipotentInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private def carry {M : Type} [AddCommGroup M] [Module ℂ M] (W Z : Submodule ℂ M) : Submodule ℂ (Module.End ℂ M) where
  carrier := {T | ∀ x ∈ W, T x ∈ Z}
  add_mem' h1 h2 x hx := Z.add_mem (h1 x hx) (h2 x hx)
  zero_mem' _ _ := Z.zero_mem
  smul_mem' c _ h x hx := Z.smul_mem c (h x hx)

theorem UpperTheory.algebraic_module_of_vanishing_block :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (S : Submodule ℂ (archSmooth K (r + s))), S ≤ NInv K (r + s) r → Centre S → ∀ (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ), AlgMod S (Van K r s) (archCapBlock D (e1 r s) τ u) ∧ AlgMod S (Van K r s) (archCapBlock D (e2 r s) τ u) := by
  intro K _ _ r s S hS hC ι _ D τ u
  have hrel : Formalism.REAL.GlRel (gen D (lam K (r + s)) τ) :=
    (UpperTheory.gen_glRelations_and_commute_of_isLie _ ι (r + s) _ D (lam K (r + s)) (isLie_lam K (r + s))).1 τ
  have hW : ∀ p q, ∀ x ∈ NInv K (r + s) r, gen D (lam K (r + s)) τ p q x ∈ NInv K (r + s) r := fun p q =>
    gen_mem D (lam K (r + s)) τ p q (carry (NInv K (r + s) r) (NInv K (r + s) r))
      fun y x hx => UpperTheory.uAction_mem_unipotentInvariant K (r + s) r _ x hx
  have hZ : ∀ (p : Fin r) (q : Fin s), ∀ x ∈ NInv K (r + s) r,
      gen D (lam K (r + s)) τ (Fin.castAdd s p) (Fin.natAdd r q) x ∈ Van K r s := fun p q =>
    gen_mem D (lam K (r + s)) τ _ _ (carry (NInv K (r + s) r) (Van K r s))
      fun y x hx => UpperTheory.archExp_single_unipotent_embedding K r s p q y x hx
  have hq : ∀ v, AlgMod S ⊥ (Formalism.REAL.qdet (gen D (lam K (r + s)) τ) v) := fun v => by
    refine UpperTheory.algMod_bot_of_mem_adjoin_commuting _ S (uAction '' ((isExpLieAlgebra K (r + s)).centerU : Set (UEnv K (r + s)))) ?_ ?_ _
      (UpperTheory.qdet_generates_universalEnveloping_centre K (r + s) ι D τ v)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact Zc_comm (uAction_mem_Zc hx) (uAction_mem_Zc hy)
    · rintro _ ⟨z, hz, rfl⟩
      exact hC z hz
  exact UpperTheory.algMod_quantumDet_leviBlocks_of_parabolic _ r s (gen D (lam K (r + s)) τ) hrel (NInv K (r + s) r) (Van K r s) S hS hW hZ hq u
