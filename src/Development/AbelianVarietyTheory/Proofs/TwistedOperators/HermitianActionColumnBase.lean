module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemLevelFunOfIsAutFun
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil GlobalTheory.LocFrame
open GlobalTheory.EmbChart (idem)
open GlobalTheory.StepData (LatFrame)
open GlobalTheory.RootEx (colE rowE)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SrcHalfOne
open GlobalTheory.EmbChart (tensAt atPlace)
open GlobalTheory.AdelicU (splitProj compFin isCMExt_host)
variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

theorem cA_cA' (z : AE D) : cA D (cA D z) = z := Formalism.L2.Theta.cA_cA z
theorem cA_alg (a : AF D.host.F) : cA D (algebraMap (AF D.host.F) (AE D) a) = algebraMap (AF D.host.F) (AE D) a := by
  change a ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]; rfl

theorem compFin_cA (z : AE D) : compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

variable (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem piW_cA_idem : piW τ (cA D (idem τ)) = 0 :=
  ((chart_piW τ).2.1 _).2 (GlobalTheory.EmbChart.isSplitIdem_idem τ).2.1

theorem piW_idem : piW τ (idem τ) = 1 := by
  change splitProj τ (compFin _ _ v (idem τ)) = 1
  rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]

theorem piW_alg (a : Fv D.host.F v) : piW τ (algebraMap (AF D.host.F) (AE D) (atPlace v a)) = a := by
  rw [(chart_piW τ).2.2.1]
  exact GlobalTheory.AdelicU.evalV_singleFin_self v a

theorem piW_cA (z : AE D) : piW τ (cA D z) = splitProj (τ.comp D.sp.cm.sig) (compFin D.host.F D.host.E v z) := by
  change splitProj τ (compFin _ _ v (cA D z)) = _
  rw [compFin_cA, GlobalTheory.AdelicU.splitProj_comp]

def plcC (y : Fv D.host.F v) : AE D := cA D (idem τ) * algebraMap (AF D.host.F) (AE D) (atPlace v y)

theorem piW_plcC (y) : piW τ (plcC τ y) = 0 := by rw [plcC, map_mul, piW_cA_idem, zero_mul]
theorem piW_cA_plcC (y) : piW τ (cA D (plcC τ y)) = y := by
  rw [plcC, map_mul, cA_cA', cA_alg, map_mul, piW_idem, piW_alg, one_mul]

theorem idem_mul_self : idem τ * idem τ = idem τ := (GlobalTheory.EmbChart.isSplitIdem_idem τ).1

section Frame

variable (V : HSp D) {ι : Type} [Fintype ι] [DecidableEq ι] (β : LatFrame (Fv D.host.F v) ι (Fin V.rank))

end Frame

section FJ

variable {V V₀ : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) {n : Type} [Fintype n] [DecidableEq n]
  {γ : LatFrame (Fv D.host.F v) n (Fin V₀.rank)} {β : LatFrame (Fv D.host.F v) (n ⊕ Fin (2 * (σ + 1))) (Fin V.rank)}
  {t : ℕ → Fv D.host.F v}

variable {τ}

open GlobalTheory.RootEx (colE rowE)

variable (hβ : IsScaled V V₀ τ d.i₀ (fourierJacobiVectors d) γ β t)
include hβ

end FJ

section Jac

variable {V V₀ L : HSp D} {σ : ℕ} (d : HypDec V V₀ (σ + 1)) (ζ : Fin L.rank → D.host.E)

end Jac
end GlobalTheory.SrcHalfOne
