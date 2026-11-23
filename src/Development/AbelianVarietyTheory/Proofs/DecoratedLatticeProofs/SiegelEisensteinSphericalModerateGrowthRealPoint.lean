module

public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero

@[expose] public section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Eis

theorem modGrowth_eis_sph : GlobalTheory.Published.SiegelEisensteinContinuation → ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  intro hP D V h0 a ha hI σ hσ
  have hμ : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hb : ResEta D 1 0 := ⟨GlobalTheory.VolHeckeCompare.exists_isEta D, fun _ _ _ => by simp⟩
  have hφ := sph_mem hI (σ : ℂ)
  obtain ⟨k, hk⟩ := (hP D V h0 a ha hI 1 0 hμ hb σ _ hφ).2 σ
  have hv := (sphConv D V a hI).eisValueAt_flat hI hφ hμ (by simpa using hσ)
  obtain ⟨r, hr, -, -, C, N, h⟩ := hk.of_eisValueAt hv
  exact ⟨C, N, fun g => hv.eisCont_eq ▸ h σ (Metric.mem_ball_self hr) g⟩

end GlobalTheory.Eis

end
