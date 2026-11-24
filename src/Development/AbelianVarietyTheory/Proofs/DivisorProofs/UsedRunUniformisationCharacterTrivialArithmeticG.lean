module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.AdelEqZeroOfOffDom
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
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TwoLevelLogarithm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

namespace GlobalTheory.ShareOn

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem uAt_chi_eq_one : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∀ (k : (uAt r v i).Comp) (la : Wt ((uAt r v i).X k).Ψ D.R.r), ∀ γ ∈ ((uAt r v i).X k).Γ, ((uAt r v i).X k).χ la γ = 1 := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ r h _ i v k la γ hγ
  exact GlobalTheory.OneEmbeddingProbe.chi_eq_one (uAt r v i)
    (fun a n hd k γ hγ => (h.laws v).p.chiTriv ((i : ℕ) + 1) ⟨Nat.le_add_left _ _, i.2⟩ _
      (r.used v).full.toCore.good_σ₀ a n hd k γ hγ) k la γ hγ

end GlobalTheory.ShareOn

end
