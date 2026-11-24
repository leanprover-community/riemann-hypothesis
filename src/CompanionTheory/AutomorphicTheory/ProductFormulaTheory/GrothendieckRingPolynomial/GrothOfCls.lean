module

public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ProdList
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.AltSum
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassGlEqClass
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleCast
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JacquetFunctionalClass
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.JhMultSegCl
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MulClassBasisRight
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.MultOne
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriCoeFlattenDecW
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.GrothendieckRingPolynomial.TriSupportedLe
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace CompanionTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hm : MulCls k := by apply mulCls
  have ha : Assoc k := by apply assoc; exact hm
  have hc : Comm k := comm k
  have h1 : One k := by apply one
  have hl : ProdList k := by apply prodList; exact hm
  refine ⟨H k, hm, ha, hc, h1, hl, tri k (H k), ?_, by apply jCls, by apply jSeg, altSum k⟩
  apply multOne <;> first | exact H k | assumption

end CompanionTheory.Groth
