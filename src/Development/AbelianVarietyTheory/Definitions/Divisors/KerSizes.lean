module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.ColRows

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

structure KerTies (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) : Prop where
  host : HostTie (ofRecord D L Del h0) t.seam t.Pr
  wts : ∃ pl : RPl D.R ≃ t.X.Tau, ∀ u, WeightTie (ofRecord D L Del h0) W pl (t.word u) (letterOf D L Del h0 u)
  chr : CharTie (ofRecord D L Del h0) t.seam W t.Ch t.glob t.sel
  an : AnalyticTie D t.δ t.χ t.cD
  mu0 : t.tup D.what₂.mu0 = 1
  sharp : (t.cst D.what₂.mu0).sharp = true
  m2 : t.m2 = D.R.m - 2
  fld : ∀ u, FieldOfDefinition W t.sel (t.tup D.what₂.mu0) (t.cst D.what₂.mu0) (t.word u) t.amb

structure KerSizes (t : KerEntTied ex) (W : Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (CY CT : ℝ) : Prop where
  sizes : Sizes t.Pr W L.sc.a
  what₂ : ∀ u, GlobalTheory.Core.Ht2.SizeRowsS CY (ofRecord D L Del h0) (letterOf D L Del h0 u)
  logT : ∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * L.sc.L

end GlobalTheory.ColRows

end
