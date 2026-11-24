module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section



section
noncomputable section
namespace GlobalTheory.PendOf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.NPin ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
end Local
def localLabelPolynomial (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k) {n : ℕ}
    (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) n) : (ZMod (D.host.g k))[X] :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  GlobalTheory.WeilDeligne.WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) n π)
def RegularLocalCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r) ρ f, InSeries D k ρ f →
    Squarefree f → (∃ x, IsLevelOne π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) D.R.r π).mono0 ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v π = f
def SplitLocalCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    ∃ (π₁ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.r)
      (π₂ : Irr ((D.naut.plGw k v).adicCompletion D.host.E) D.R.t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin D.R.t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (idemOf D k ρ) y
def LocalDatumCondition (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (χ : ((D.naut.plGw k v).adicCompletion D.host.E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (u : ZMod (D.host.g k)) (π : Irr ((D.naut.plGw k v).adicCompletion D.host.E) (D.R.r + D.R.t)) ρ f,
    IsTame χ → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 χ hχ) = X - C u → InSeries D k ρ f → Squarefree f → ¬ f.IsRoot u →
    (∃ x, IsBlockVec χ π.π x ∧ NotKilled π.π (idemOf D k ρ) x) →
    (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ π).mono0 ∧ _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v π = f * (X - C u) ^ D.R.t
end GlobalTheory.PendOf
end
end
