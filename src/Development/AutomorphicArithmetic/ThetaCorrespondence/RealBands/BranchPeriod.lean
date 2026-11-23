module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLossStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodNonvanishingOfArchimedeanInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchPack
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.Period
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

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Branch

theorem periodNe_of_eigen : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    GlobalTheory.Published.CuspRapidDecay → RealInputE → PeriodNe := by
  intro hHC hCW hCR hR
  have h0 := Cusp.exists_cusp_form_theta_period_ne_zero hHC hCW hCR (packEx_of_eigen hR) GlobalTheory.T.gridDepth_pays_every_loss
  intro ε CF hCF
  obtain ⟨x, hx⟩ := h0 ε CF hCF
  refine ⟨x, fun D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0 w w0 => ?_⟩
  obtain ⟨y, hy, v, w', hp⟩ := hx D large₂ e a b T L μ0 hL G W M hM M₀ MP t ht t0
  obtain ⟨a', ha', hp'⟩ := GlobalTheory.PeriodNePf.exists_kf W M hM hCR hHC M₀ MP ht hy v w' hp w w0
  exact ⟨y, hy, a', ha', hp'⟩

end UpperTheory.Lit.Branch

end
