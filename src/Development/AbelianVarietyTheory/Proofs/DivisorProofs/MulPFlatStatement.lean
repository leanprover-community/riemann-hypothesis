module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteFaithfullyFlatKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPEqOfTranslInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslCoactionFreeCoassocCounital
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

@[expose] public section

open scoped TensorProduct

theorem _root_.GlobalTheory.T.mulP_flat' : ∀ (p : ℕ) (R : Type) [CommRing R] (G : GlobalTheory.PDivGroup p R) (n : ℕ), RingHom.Flat ((G.mulP n : G.A n →ₐ[R] G.A (n + 1)) : G.A n →+* G.A (n + 1)) := by
  intro p R _ G n
  obtain ⟨hassoc, hcounit, hsurj⟩ := G.transl_free n
  obtain ⟨-, -, hff, -⟩ :=
    GlobalTheory.HopfQuot.finite_faithfullyFlat_ker (G.transl n) hassoc hcounit hsurj
  let B := AlgHom.equalizer (G.transl n)
    (Algebra.TensorProduct.includeLeft : G.A (n + 1) →ₐ[R] G.A (n + 1) ⊗[R] G.A 1)
  let f : G.A n →ₐ[R] B := AlgHom.codRestrict
    (G.mulP n : G.A n →ₐ[R] G.A (n + 1)) B (fun a => G.transl_mulP n a)
  have hf : Function.Bijective f := by
    refine ⟨fun a b h => GlobalTheory.PDivGroup.Test.mulP_injective G n
      (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨a, ha⟩ := G.exists_mulP_eq_of_transl_eq n y.1 y.2
    exact ⟨a, Subtype.ext ha⟩
  have hB : RingHom.Flat (algebraMap B (G.A (n + 1))) := by
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have hflat : RingHom.Flat (f : G.A n →+* B) := RingHom.Flat.of_bijective hf
  convert RingHom.Flat.comp hflat hB using 1
  exact RingHom.ext fun a => rfl
