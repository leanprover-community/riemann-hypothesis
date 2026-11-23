module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataDefiniteModelsNonempty
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

theorem _root_.GlobalTheory.T.thetaArchimedeanData_definiteModels_nonempty : ∀ (D : D7) (T : Top D) (h : LawsP T) (EX : ErrX D) (p : ℕ) (hj : InR D D.R.m) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D D.R.m) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), ParOK T EX p D.R.m → PageOK large₂ (recPJ h D.R.m hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h D.R.m hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ (N : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp D.R.m wL), NoCommonZero (T.Q.Xo D.R.m) T.Q.c (fun i => (w i).1) → Nonempty (GlobalTheory.Shares.ArchAt h D.R.m w wF Tn 1) := by
  first | exact @GlobalTheory.ArchDefinite.archAt_nonempty_of_definite | exact GlobalTheory.ArchDefinite.archAt_nonempty_of_definite | (intros; apply GlobalTheory.ArchDefinite.archAt_nonempty_of_definite <;> assumption)
