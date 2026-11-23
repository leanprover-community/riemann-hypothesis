module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupReal

open Formalism.L2.Pj Formalism.IndefR.FWT GlobalTheory.HeckeSup



theorem hkSupAt_realSide : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → ∀ (D : D7) (X : RealSide D) j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j := by
  intro hDec hI hT hRT D X i
  have hC := X.char
  have ht : TieIn X.core X.R.toRealDat X.geo.κ X.geo.v₀ :=
    ⟨X.geo.fw.laws, X.geo.fw.alg_eq, X.geo.fw.kap, X.geo.fw.hv₀, X.geo.fw.chiR, X.geo.fw.x0⟩
  have h5 : GlobalTheory.Core5 X.R.toRealDat X.F.lv2 := ⟨hC.lev, hC.grp, hC.fam, hC.models, hC.thP⟩
  have hio := GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hr := GlobalTheory.OneMapTies.oneMapRow0_of_ties_ofFive GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core X.R.toRealDat X.F.lv2
    X.geo.κ X.geo.v₀ h5 ht hio X.geo.O i (X.geo.pins i)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.constPinned_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.geo.O i (X.geo.pins i) hr (X.geo.cTie i)
  have h0 := GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.readAt0_of X.core X.R.toRealDat X.geo.κ X.geo.v₀ X.inGeo.jEvExists X.geo.fw X.unif i hc
  have hsp := GlobalTheory.AdSpan.spanAt X.R.toRealDat hDec X.size hC.lev hC.fam hC.models hC.thP i X.A3.A.μ0
  refine hkSupAt_of_clauses hI hT GlobalTheory.HeckePointLaw.heckePointLaws (hC.lev.βW i) hC.fam.Sb hC.models.inf hC.models.HW
    hC.models.gW hC.models.HV hC.models.jV hC.thP.thF_mem X.geo.fw h0 hsp (fun O hO => ?_) fun c' hL hV => ?_
  · obtain ⟨cc, h1, u, h2, h3, h4, -⟩ := GlobalTheory.AdTh.ioExt_oneMap_ofFive.2.1 GlobalTheory.ChartFree.chartIndep D _ _ _ _ X.core
      X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ h5 ht hio i _ _ O hO
    exact ⟨cc, h1, u, h2, h3, h4⟩
  · exact @hRT D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.F.lv2 X.geo.κ X.geo.v₀ hC.lev hC.grp
      hC.fam hC.models hC.thP
      (@TieIn.mk D X.Γ _ _ X.Pl0 _ X.A3.A (withConst X.core c') X.alg X.R.toRealDat X.geo.κ X.geo.v₀ hL X.geo.fw.alg_eq
        X.geo.fw.kap X.geo.fw.hv₀ X.geo.fw.chiR X.geo.fw.x0) i _ rfl hV

end GlobalTheory.HeckeSupReal
