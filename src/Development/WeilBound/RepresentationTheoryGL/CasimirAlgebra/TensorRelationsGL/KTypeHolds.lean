module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChain
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PCurry
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PHeight
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PJmComm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PPiQdet
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PQdetFacts
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSemiZero
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSpectrum
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepChar
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFin
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransOf
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallQuot
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem kType_holds : KType := by
  have tg := tensorGl_holds
  have jm := jmComm_of tg
  have cu := curry_holds
  have qd := qdetFacts_holds
  have pq := piQdet_of tg jm
  have sf := stepFormula_of tg jm pq cu
  have sc := stepChar_of tg sf qd
  have sp := spectrum_of tg jm cu sc
  have ht := height_of tg
  have wq := wallQuot_of qd
  have ch := chain_of tg jm cu sf qd sc ht wq
  have ca := colAnti_of tg jm ht
  have tf := transFin_of tg jm sf qd sp ch ca
  have tr := trans_of tf
  have ta := transAll_of tg tr
  have tk := tensorGK_of tg
  have wa := wallAlg_of tg jm qd sp
  have li := lieInv_holds
  have co := contract_of tg qd wa tk li wq
  have sz := semiZero_of qd wa li wq
  have sa := sphAll_of swStart_holds co sz
  exact kType_of tg ta tk sa young_holds

end PositivityTheory.Rg.Cz
