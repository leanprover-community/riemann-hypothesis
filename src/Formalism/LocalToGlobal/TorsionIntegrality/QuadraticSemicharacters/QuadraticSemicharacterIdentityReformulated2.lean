module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.LineTransport
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharactersFactVersion
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SemiCharBasic
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.IteratedDerivLine
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LineRestrLinSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.NormLtOne
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.QuadraticSemicharactersOfProductThetaMem
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.L2.Th1.H

theorem opUMul : OpUMul := heisenbergMul
theorem opUComm : OpUComm := heisenbergComm
theorem opUIsom : OpUIsom := heisenbergIsometry
theorem pullOpU : PullOpU := precompHeisenberg
theorem semiCharBasic : SemiCharBasic := semicharacterBasic
theorem semiHom : SemiHom := semicharacterHom
theorem opUAnalytic : OpUAnalytic := heisenbergAnalytic
theorem matHBasic : MatHBasic := matrixFormBasic
theorem stdHBasic : StdHBasic := standardFormBasic
theorem opUStd : OpUStd := heisenbergStandard
theorem opUBlk4 : OpUBlk4 := heisenbergFourfold

theorem interClass : InterClass := InterClass_of semiHom
theorem repsExist : RepsExist := cosetRepsExist
theorem interReps : InterReps := InterReps_of semiHom
theorem interFixed : InterFixed := InterFixed_of semiHom
theorem interTh : InterTh := InterTh_of semiHom opUAnalytic
theorem thIsom : ThIsom := ThIsom_of opUIsom
theorem charSum : CharSum := characterSum
theorem indexEq : IndexEq := IndexEq_of charSum repsExist
theorem interInv : InterInv := InterInv_of opUComm interReps interFixed repsExist
theorem lineTransport : LineTransport := LineTransport_of interInv interTh

theorem stdSelfDual : StdSelfDual := StdSelfDual_proof
theorem stdSemiChar : StdSemiChar := StdSemiChar_proof
theorem product_theta_mem' : ProductThetaMem := product_theta_mem
theorem thStd : ThStd := ThStd_proof
theorem tens4Mem : Tens4Mem := fourfoldTensorMem
theorem fourthRoot : FourthRoot := fourth_root
theorem alphaQSemi : AlphaQSemi := quadMultiplierSemicharacter
theorem alphaQRules : AlphaQRules := quadMultiplierRules
theorem thetaVector : ThetaVector :=
  ThetaVector_of lineTransport thStd product_theta_mem' stdSelfDual stdSemiChar thIsom fourthRoot

theorem lineUnique : LineUnique := lineUnique'
theorem taylorLine : TaylorLine := taylorLine'
theorem taylorMvLinear : TaylorMvLinear := TaylorMvLinear_of lineUnique taylorLine
theorem taylorMvMul : TaylorMvMul := TaylorMvMul_of lineUnique taylorLine
theorem taylorMvComp : TaylorMvComp := TaylorMvComp_of lineUnique taylorLine
theorem taylorMvProd : TaylorMvProd := TaylorMvProd_of lineUnique taylorLine
theorem taylorMvTens4 : TaylorMvTens4 := TaylorMvTens4_of lineUnique taylorLine
theorem taylorMvInj : TaylorMvInj := TaylorMvInj_of lineUnique taylorLine

theorem quadraticSemicharacter_identity_reformulated₂ : quadraticSemicharacterIdentityReformulated₂ := quadraticSemicharacters_of_productThetaMem product_theta_mem'
theorem quadraticSemicharacters_fact : quadraticSemicharacterIdentity :=
  quadraticSemicharacterIdentity_of_reformulated_of_taylorMv_of_repsExist_of_opUAnalytic quadraticSemicharacter_identity_reformulated₂ taylorMvLinear taylorMvComp taylorMvProd taylorMvTens4 repsExist opUAnalytic

end Formalism.L2.Th1.H
