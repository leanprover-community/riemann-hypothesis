module

public import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP

@[expose] public section

open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_hopf_quotient_ker_eq_torsionIdeal :
    ∀ (O : Type) [CommRing O] (B : Type) [CommRing B] [HopfAlgebra O B] [IsCocomm O B] (n : ℕ),
      ∃ (D : Type) (_ : CommRing D) (_ : HopfAlgebra O D) (_ : IsCocomm O D) (π : B →ₐc[O] D),
        Function.Surjective π ∧ RingHom.ker π = torsionIdeal (R := O) (A := B) n := by
  intro O _ B _ _ _ n
  let I := torsionIdeal (R := O) (A := B) n
  have : I.IsHopfIdeal O :=
    isHopfIdeal_kerIdeal_of_bialgHom O B B (mulBy (R := O) (A := B) n)
  let π : B →ₐc[O] B ⧸ I := Bialgebra.Quotient.mkBialgHom I
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have cocomm : IsCocomm O (B ⧸ I) := by
    constructor
    ext b
    obtain ⟨a, rfl⟩ := hπ b
    change TensorProduct.comm O (B ⧸ I) (B ⧸ I) (comul (π a)) = comul (π a)
    rw [← CoalgHomClass.map_comp_comul_apply π a, ← TensorProduct.map_comm, comm_comul]
  exact ⟨B ⧸ I, inferInstance, inferInstance, cocomm, π, hπ,
    Ideal.ext fun _ => Ideal.Quotient.eq_zero_iff_mem⟩
