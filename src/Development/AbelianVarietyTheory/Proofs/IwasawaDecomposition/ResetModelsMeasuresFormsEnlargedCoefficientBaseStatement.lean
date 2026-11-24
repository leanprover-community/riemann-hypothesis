module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CrdOver
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RSideA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResetModelsMeasuresFormsEnlargedCoefficientBase
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.reset_modelsMeasuresForms_enlargedCoefficientBase : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → ∀ (core' : Formalism.L2.Pj.CoreJ (w'.st Z').toD7) [Algebra core'.Q.c.F (w'.st Z').toD7.what₂.LL],
    (∀ y : core'.Q.c.F, B'.embLL (algebraMap core'.Q.c.F (w'.st Z').toD7.what₂.LL y) = (y : ℂ)) →
    HEq core'.Q.H z.core.Q.H → HEq core'.Q.l z.core.Q.l → HEq core'.Q.c z.core.Q.c →
    ∀ {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px} (R : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG : G0 R.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R cG → RSideA z Wt' R →
    ∃ (R₁ : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) core'.Q.c.F) (cG₁ : G0 R₁.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd), Kept T' w' Z' hX' Wt' R₁ cG₁ ∧ RSideW z Wt' R₁ := by
  first | exact @GlobalTheory.Mem.R3.Rw.resetW | exact GlobalTheory.Mem.R3.Rw.resetW | (intros; apply GlobalTheory.Mem.R3.Rw.resetW <;> assumption)
