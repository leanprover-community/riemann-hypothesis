module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReadPk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumComplexRowFormColumnsLevelEq
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI GlobalTheory.Mem.Col2.starE
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.classSum_complexRowForm_columnsLevel_eq : ∀ (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok)
    (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (a : I.ι) (y : Fin (mAU X I hX Xg tr true a).n → X.B.LL)
    (x : Formalism.L2.Col.MtildeV (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) (TC.Ps I)),
    IsFormOf (Pr := X.B.primes px) X.B.wts I.Ch I.sel (I.tup a) hX (TC.Ps I) x
      (rowForm (D := X.toD7) (famR X I hX Set.univ Xg tr).A (lev1 I) (chr1 I) (tAll I a) y) →
    Df.cSum I hX a (Df.toCx I hX a x) (Df.toCx I hX a x) = X.B.embLL (Formalism.DivisionValues.hform (mAU X I hX Xg tr true a).H y y) := by
  first | exact @GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | exact GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm | (intros; apply GlobalTheory.Mem.CsumForm.cSum_toCx_rowForm <;> assumption)
