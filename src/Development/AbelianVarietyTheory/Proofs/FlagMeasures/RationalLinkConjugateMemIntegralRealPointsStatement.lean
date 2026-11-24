module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalLinkConjugateMemIntegralRealPoints
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Matrix

theorem _root_.GlobalTheory.T.rationalLink_conjugate_mem_integralRealPoints : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (u u' : D.what₂.Word) (s : TT Y u u') (n : (VS D).V ≃ₗ[D.host.E] (VS D).V), n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) → ∃ x : X.B.I.GA, Formalism.L2.SG.TermOp.RatLink X x ((W.δ u)⁻¹ * n * W.δ u) ∧ x.1 ∈ Formalism.L2.SG.TermOp.ROinf s := by
  first | exact @GlobalTheory.CoverAct.ratLink_mem_ROinf | exact GlobalTheory.CoverAct.ratLink_mem_ROinf | (intros; apply GlobalTheory.CoverAct.ratLink_mem_ROinf <;> assumption)
