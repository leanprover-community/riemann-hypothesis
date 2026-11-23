module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacedBy
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducesToResidueOfLocalLevelElementMovedBack
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.reducesToResidue_of_localLevelElement_movedBack : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E) (b : GA D (c.V 0)) (β : GL (Fin (c.V 0).rank) (Lev.EAf D)), GlobalTheory.LevZero.LocAt G PP b β → b ∈ GfC (c.V 0) → ∀ (hr : D.R.r ≤ (c.V 0).rank) (g : GA D (c.V 0)) (x : G.S.P.J), (ofSplit G.q).IsLoc (G.FY 0 (G.s + 1) (Nat.zero_add _)) g (GlobalTheory.LevZeroGen.upZero G.S (Fin D.R.t) x.1) → finE (c.V 0) (b⁻¹ * g * b) ∈ Formalism.L2.DIV.St β → GlobalTheory.LevZero.Red G PP x (upperLeftBlock hr (redFn β PP (finE (c.V 0) (b⁻¹ * g * b)))) := by
  first | exact @GlobalTheory.LevZeroFamRead.red_of_isLoc | exact GlobalTheory.LevZeroFamRead.red_of_isLoc | (intros; apply GlobalTheory.LevZeroFamRead.red_of_isLoc <;> assumption)
