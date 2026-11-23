module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyBijectiveOfSupportBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientLongExactSequenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeZeroOfDvd
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.EtaleDualityTraceIsomorphism
public import Development.EtaleCohomology.EtaleDuality.FinAdicFin
public import Development.EtaleCohomology.WeilConjectures.AdicFinPf
public import Development.EtaleCohomology.WeilConjectures.AdicKerPf
public import Development.EtaleCohomology.WeilConjectures.FinQCut
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
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.G3

theorem vFin_holds : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hT : ∀ a m, Finite (Ht (l ^ a) (sch.obj X) m i) := fun a m => by
    have : NeZero (l ^ a) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact UpperTheory.Et.etale_finiteness_of_duality (l ^ a) k (by rw [Nat.cast_pow]; exact hl.pow a) p m i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l _ n i (fun a => hT a n)
      (LateralTheory.EWeil.AdicKerPf.AdicKer_of GlobalTheory.EtC.RedCoef.a11 l _ i
        (fun b => LateralTheory.Fin.AdicFin.etale_bockstein_sequence_adic_finiteness GlobalTheory.T.etaleCohomology_coefficient_longExactSequence GlobalTheory.T.etaleCohomology_coefficientRing_invariance GlobalTheory.T.etaleCohomology_bijective_of_support_bijective GlobalTheory.EtC.RedCoef.a11 l b _ i
          (LateralTheory.EWeil.FinQCut.inv_of_over hl p)) hT n)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.G3

end
