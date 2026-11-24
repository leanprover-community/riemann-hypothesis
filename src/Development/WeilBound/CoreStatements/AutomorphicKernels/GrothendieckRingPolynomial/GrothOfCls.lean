module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.AltSum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassGlEqClass
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleCast
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleFold
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ClassProductIrreducibleLeft
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.JacquetFunctionalClass
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.JhMultSegCl
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MulClassBasisRight
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.MultOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriCoeFlattenDecW
public import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.TriSupportedLe
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

namespace PositivityTheory.Groth

theorem groth_of_cls (H : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Cls k) :
    GlobalTheory.Published.GrothendieckRingPolynomial := by
  refine groth_of_steps (fun k _ _ _ _ => ?_) triAut uniTri
  have hc := H k
  have hm := mulCls k
  have ha := assoc k hm
  have hco := comm k
  have ho := one k
  have hp := prodList k hm
  exact ⟨hc, hm, ha, hco, ho, hp, tri k hc, multOne k hc hm ha hco ho hp, jCls k, jSeg k, altSum k⟩

end PositivityTheory.Groth
