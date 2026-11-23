module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ExistsIdempotentHeckeOperatorWithRegularSupportAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryInertOddPrime
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.CnjApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.RelIndexNeZeroOfOpen
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecData
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.ValOfNotMem
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

theorem UpperTheory.Gal.Spc.specTopG :
    UpperTheory.Gal.Int.Geo.Pl.WtOf → UpperTheory.Gal.Spc.SpecTopG := by
  intro hW E _ _ _ A n p _ S F x U w₀ Up V hodd hsc hgen hoff hq X
  obtain ⟨r, W, hrX, haux⟩ := UpperTheory.Gal.Spc.auxiliary_prime_holds E A n p S x U w₀ Up V hgen X
  refine ⟨r, haux.prime, hrX, haux.ne, ?_⟩
  intro N hrN hst J g θ hseen
  obtain ⟨L, hw, Ty, hTy⟩ := UpperTheory.Gal.Spc.tyEx E A n p S F x U w₀ Up V hoff r W haux N hrN hst
  have hx : UpperTheory.Gal.Spc.Extra S F.j := by
    rw [F.j_tr]
    exact ⟨fun w hp => UpperTheory.Gal.Spc.plTr E A n p S F.tr w hp,
      fun q hq' hqp g hg => UpperTheory.Gal.Spc.regTr E A n p S F.tr q hq' hqp g hg⟩
  exact UpperTheory.Gal.Spc.specData hW E A n p S F x U w₀ Up V hodd hsc hgen hoff hq r W haux N hrN hst
    L hw Ty hTy hx J g θ hseen
