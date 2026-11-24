module

import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK
import Formalism.DoubleCosetMeasures.Statement
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.ToIdeleSq
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic

@[expose] public section

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_cancel {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hab : IsUnram (a * b)) : IsUnram b := fun x hx => by
  have h := hab x hx
  rwa [MonoidHom.mul_apply, ha x hx, one_mul] at h

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem unr_inv {a : kˣ →* ℂˣ} (ha : IsUnram a) : IsUnram a⁻¹ := fun x hx => by
  rw [MonoidHom.inv_apply, ha x hx, inv_one]


private theorem lin_zero (a : kˣ →* ℂˣ) : (lin a).eval 0 = 1 := by
  unfold lin
  split_ifs <;> simp

end Loc

private theorem unrAt_iff {F : Type} [Field F] [NumberField F] (χ : HChar F) (w : HeightOneSpectrum (𝓞 F)) :
    χ.UnrAt w ↔ IsUnram (χ.loc w) := by
  haveI : (Valued.v : Valuation (w.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  refine forall_congr' fun x => imp_congr_left ?_
  exact (ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion F)) Valued.v).eq_one_iff_eq_one.symm

private theorem unr_iff (u : Ad3.Pl) (a : (u.adicCompletion ℚ)ˣ →* ℂˣ) : IsUnramifiedChar a ↔ IsUnram a := by
  haveI : (Valued.v : Valuation (u.adicCompletion ℚ) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [isUnramifiedChar_iff]
  refine forall_congr' fun x => imp_congr_left ?_
  rw [Ad3P.DihedralUnramifiedPlaces.ord_eq u x.ne_zero, neg_eq_zero,
    (ValuativeRel.isEquiv (ValuativeRel.valuation (u.adicCompletion ℚ)) Valued.v).eq_one_iff_eq_one]
  have h0 : Valued.v (x : u.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  constructor
  · intro h
    rw [← WithZero.exp_log h0, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

private theorem under_eq {K : Type} [Field K] [NumberField K] {p : Ad3.Pl} (w : PlacesOver K p) : w.1.under (𝓞 ℚ) = p :=
  HeightOneSpectrum.ext w.2.over.symm

private theorem exists_above (K : Type) [Field K] [NumberField K] (S : Finset Ad3.Pl) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 K)), ∀ w, w ∈ T ↔ w.under (𝓞 ℚ) ∈ S := by
  refine ⟨S.biUnion fun p => (Finset.univ : Finset (PlacesOver K p)).map (Function.Embedding.subtype _), fun w => ?_⟩
  simp only [Finset.mem_biUnion, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp, w', rfl⟩
    change w'.1.under (𝓞 ℚ) ∈ S
    rwa [under_eq]
  · exact fun h => ⟨_, h, ⟨w, ⟨rfl⟩⟩, rfl⟩

private theorem tri_pow (a x : ℂˣ) (f : ℕ) :
    ((({a ^ f, 1, (a ^ f)⁻¹} : Multiset ℂˣ).map (· * x ^ f)).map fun b : ℂˣ => (b : ℂ)) = (tri a x).map (· ^ f) := by
  simp [tri, mul_pow]
