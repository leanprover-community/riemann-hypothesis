module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelTracedSeriesRational
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
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adForm_eq_levelTrace_singleSeries : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ h ∈ GfC (Vc (Fm.D x i) j), ∀ w' : ((R2 p).cV j).W, InCoefLat (R2 p) j h w' →
  ∃ y ∈ Submodule.span (Fm.D x i).what₂.LL ((p.nexp.fi j).e '' ((p.Sx.A ((j : ℕ) + 1)).WK : Set _)), ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j y (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) h w' v) := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | exact _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' | (intros; apply _root_.GlobalTheory.BigOn.Exp.adForm_eq_levelTrace_singleSeries' <;> assumption)
end
