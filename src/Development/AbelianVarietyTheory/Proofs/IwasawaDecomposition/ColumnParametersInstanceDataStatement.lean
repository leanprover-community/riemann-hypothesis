module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParamsInstanceData
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Tr

theorem _root_.GlobalTheory.T.column_params_instance_data : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L) (Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC) (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : RowsT K w Z Wt ex.p0), AmbAre t.r.Z ex.amb ex.amb0 → MjAre t.r.Z Yd → GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG) → (∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v) → ∀ Dc Sp₀ Zsc₀ (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((t.r.Y))) (Sp : ∀ Zs, SPer (Dc Zs)) Zsc (sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] (Sp (zsOf t.r.z.R t.r.z.F)).HH), ∃ a : TwArgs ex t, a.Dc = Dc ∧ HEq a.Sp Sp ∧ a.Zsc = Zsc ∧ HEq a.x.sEE sEE ∧ HEq a.x.C.wU C₀.wU ∧ HEq a.x.C.eNu C₀.eNu ∧ GlobalTheory.RealGeo.InGeo a.x.geo := by
  first | exact @GlobalTheory.Mem.R3.twArgs_exists | exact GlobalTheory.Mem.R3.twArgs_exists | (intros; apply GlobalTheory.Mem.R3.twArgs_exists <;> assumption)
