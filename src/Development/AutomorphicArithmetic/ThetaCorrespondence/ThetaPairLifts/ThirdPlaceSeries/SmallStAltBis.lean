module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealTwLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicPolynomialLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapVVSymmMapVV
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



section
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain
open NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links (PolF labLL)
open Formalism.L2.Host (embLL0)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SmallSpan
variable {D : D7} {m n : ℕ}
theorem smallSt_alt : _root_.GlobalTheory.BigOn.Exp.TupLe.SmallnessCondition := by
  intro D _ _ _ _ _ _ _ _ _ p j _ _ B hB _ O O' _ hO' h P hP
  exact harmLat_le_span D.LL0.val.toRingHom D.what₂.embLL (labLL0 D) O O' hO'.int B.w B.F.BS hB.wt
    (GlobalTheory.CoefLatConj.pq_le hB) (isLattice_latAt hB.frame _) hP
end GlobalTheory.SmallSpan
end
end
