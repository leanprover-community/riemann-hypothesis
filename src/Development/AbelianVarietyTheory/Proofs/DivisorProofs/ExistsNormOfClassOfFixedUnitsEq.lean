module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.UnitLemma.InvAlg.ClRel

theorem eq_of_mk_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (x y : {x : B.Aˣ // B.σ (x : B.A) = x}), (Quot.mk _ x : B.Cl) = Quot.mk _ y → ∃ a : B.Aˣ, (y.1 : B.A) = x.1 * (a * B.σ a) := by
  intro K B x y h
  have hsu : ∀ u : B.Aˣ, B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A) = 1 := fun u => by
    rw [← map_mul, Units.mul_inv, map_one]
  have heq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      rw [hu]
      calc (x.1 : B.A) = (x.1 : B.A) * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) *
            (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by rw [hsu, Units.mul_inv, one_mul, mul_one]
        _ = _ := by ring
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]
      ring
  exact (heq.eqvGen_iff).mp (Quot.eqvGen_exact h)

end GlobalTheory.UnitLemma.InvAlg.ClRel
