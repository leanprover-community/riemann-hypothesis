module

public import Development.EtaleCohomology.EtaleSheaves.LevelIdentPf
public import Development.EtaleCohomology.EtaleSheaves.longPf
public import Development.EtaleCohomology.EtaleSheaves.stupidPf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
public import Development.EtaleCohomology.EtaleSheaves.CochainComplexSingleFunctorZeroMapFZero
import Development.EtaleCohomology.EtaleSheaves.DescentInduction.Bounds
import Development.EtaleCohomology.EtaleSheaves.inclPf
import Development.EtaleCohomology.EtaleSheaves.longPfSes
import Development.EtaleCohomology.EtaleSheaves.shiftPf
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

namespace UpperTheory.Et.EtaleDescentEtaleAxioms

theorem a0 : LateralTheory.E.LevelIdentPf.FreeSingleHomotopyEquivDiscreteChains := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf
theorem a1 : LateralTheory.E.DescStepPf.LevelIdent := LateralTheory.E.LevelIdentPf.LevelIdent_of a0
theorem a2 : LateralTheory.E.stupidPf.trunc0 := LateralTheory.E.trunc0Pf.trunc0_of
theorem a3 : LateralTheory.E.stupidPf.incl := LateralTheory.E.inclPf.incl_of
theorem a4 : LateralTheory.E.CxDescPf.stupid := LateralTheory.E.stupidPf.stupid_of a2 a3
theorem a5 : LateralTheory.E.longPf.LES := GlobalTheory.T.hypercohomology_longExact_first_of_injective
theorem a6 : LateralTheory.E.CxDescPf.long := LateralTheory.E.longPfSes.long_of a5
theorem a7 : LateralTheory.E.CxDescPf.shift := LateralTheory.E.shiftPf.shift_of
theorem a8 : LateralTheory.E.DescStepPf.CxDesc := LateralTheory.E.CxDescPf.CxDesc_of a4 a6 a7
theorem a9 : LateralTheory.E.t_E1Cut.DescStep := LateralTheory.E.DescStepPf.etale_descent_induction_of_levelwise_identity_and_complex_descent a1 a8

theorem intersectionNumber_baseChange : LateralTheory.E.t_E1Cut.DescStep := a9

end UpperTheory.Et.EtaleDescentEtaleAxioms
