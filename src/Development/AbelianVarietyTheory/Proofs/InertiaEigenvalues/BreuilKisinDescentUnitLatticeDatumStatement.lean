module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentUnitLatticeDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.breuilKisinDescent_unitLattice_datum : GlobalTheory.Published.BhattScholzeCrystallineLattices → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (Pk : Pack a ϖ η H (unitLat (Gl l) : QLat LL)), ∃ (u : ME Pk.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) ∧ u.1 ∈ Pk.D.Minv ∧ Pk.D.phi u.1 = u.1 ∧ toW (thetaW a LL) ϖ Pk.D.toPhiMod u = Pk.R.I.ofT x := by
  first | exact @GlobalTheory.BKGal.UnitDatum.main | exact GlobalTheory.BKGal.UnitDatum.main | (intros; apply GlobalTheory.BKGal.UnitDatum.main <;> assumption)
