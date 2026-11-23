module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplittingPreservesLocalSchwartz
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

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.splitting_preserves_local_schwartz : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {Bf : W → W → AF F} {κ : Type} [Fintype κ]
    (dd : Darboux Bf κ) (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ {G : Type} [Group G] (act : G → W → W) (om : G →* Module.End ℂ ((κ → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    ∀ (v : Pl (F := F)) (p : G), (∀ u, At (evFin F v) u → At (evFin F v) (act p u)) →
    (∀ Φ ∈ SB (κ → Fv F v), ∃ Φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (om p) Φ Φ₁) →
    ∃ S : ((κ → Fv F v) → ℂ) → (κ → Fv F v) → ℂ,
      (∀ Φ ∈ SB (κ → Fv F v), S Φ ∈ SB (κ → Fv F v) ∧ Acts (evFin F v) (om p) Φ (S Φ)) ∧
      ∀ u, At (evFin F v) u → ∀ Φ ∈ SB (κ → Fv F v),
        S (schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v u) Φ) =
          schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo dd v (act p u)) (S Φ) := by
  exact @GlobalTheory.LocSplitOp.exists_locOp
