module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology
open scoped Classical

noncomputable section

namespace GlobalTheory.ThetaIntegralLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_om_one (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (k h : UA σ W.J) :
    M.I om (om (1, k) Φ) h = M.I om Φ (h * k) := by
  unfold Model.I theta
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (om (1, k) Φ)) = thetaSum F (om (g, h * k) Φ)
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem I_smul (M : Model σ Y W) (om : Rep σ Y W) (c : ℂ) (Φ : Fn F n d) (h : UA σ W.J) :
    M.I om (c • Φ) h = c * M.I om Φ h := by
  unfold Model.I theta
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (c • Φ)) = c * thetaSum F (om (g, h) Φ)
  rw [map_smul, thetaSum_smul]

theorem I_add (M : Model σ Y W) (om : Rep σ Y W) (hpres : ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), om x Φ ∈ schA F (Fin n × Fin d))
    (hconv : ∀ Φ ∈ schA F (Fin n × Fin d), M.Conv om Φ) {Φ Ψ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d))
    (hΨ : Ψ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J) : M.I om (Φ + Ψ) h = M.I om Φ h + M.I om Ψ h := by
  unfold Model.I
  rw [← integral_add (hconv Φ hΦ h) (hconv Ψ hΨ h)]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  show thetaSum F (om (g, h) (Φ + Ψ)) = thetaSum F (om (g, h) Φ) + thetaSum F (om (g, h) Ψ)
  rw [map_add (f := _), thetaSum_add F (hpres _ _ hΦ) (hpres _ _ hΨ)]

theorem snd_eq_zero_of_at {κ : Type} (z : κ → AF F) (hz : At (evI F) z) (i : κ) : (z i).2 = 0 := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) * (z i).2 = 0 := congrArg Prod.snd (congrFun (hz u hu) i)
  rwa [one_mul] at h1

end GlobalTheory.ThetaIntegralLine
