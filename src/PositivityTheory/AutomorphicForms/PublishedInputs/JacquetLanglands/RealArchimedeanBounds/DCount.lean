module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf
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
import Mathlib.Tactic.NormNum.Prime
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AAdd
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ABnfHP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMinkP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AMonoP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AOrb
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATransP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.AUnitP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DCountP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DEntryP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DGoodP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DMinkP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DNormalP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DProdP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DScaleP
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.DetR
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IntegralTransvectionMemSlIntegersConjugateZero
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.IwasawaDecompositionFiniteAdeles
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.JFSa
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.MapScalarCenter
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.PlaceEq
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFMul
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowFSmul
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.RowMul
public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.VOne

@[expose] public section

namespace UpperTheory.Esk

theorem dAx : DAx :=
  have m := aMem
  have iw := aIw m
  have row := aRow m iw
  have orb := aOrb m
  have bnf := aBnfH (aBnf m iw aCls (aAdd m)) orb
  have ht := dHt row
  have mul := dMul m iw aMono row
  dAx_of (dCount m bnf orb) ht mul (dProd m aMono row) (dMink m aMono row bnf aMink ht mul)
    (dNormal m bnf orb aUnit aTrans ht mul) (dCnt (dScale m aCls aUnit) dBox dEntry)

theorem dTwo' : DTwo := dTwo aMem

theorem dGood' : DGood := dGood aMem

end UpperTheory.Esk
