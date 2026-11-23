module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelGroupWithCharacterAtTypePlaces
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_levelGroup_with_character_at_type_places : ∀ (D : D7) (T : TwR D.LL0 D.nd) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ)
    (i : T.Tw) (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (T.Ok i k)ˣ)
    (QP DP : Finset (PlE D.host)) (sp : PlE D.host → SplitPlace D.host.E)
    (redG : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk),
      (sp (NX.pG D kv)).v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1)),
    (∀ P, (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (sp P).w = P) →
    (∀ P P', (P ∈ QP ∨ P ∈ DP ∨ ∃ kv, P = NX.pG D kv) → (P' ∈ QP ∨ P' ∈ DP ∨ ∃ kv, P' = NX.pG D kv) →
      (sp P).v = (sp P').v → P = P') →
    (∀ P ∈ QP, P ∉ DP) → (∀ kv, NX.pG D kv ∉ QP ∧ NX.pG D kv ∉ DP) → (∀ kv kv', NX.pG D kv = NX.pG D kv' → kv = kv') →
    QP ⊆ Q → DP ⊆ T.pD i →
    (∀ P ∈ QP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal ψ P 1 (u * u') = NX.tameVal ψ P 1 u * NX.tameVal ψ P 1 u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal → NX.tameVal ψ P 1 u = NX.tameVal ψ P 1 u') →
    (∀ P ∈ DP, (∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u' ∉ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) (u * u') =
          NX.tameVal (T.delta i) P (if b then 1 else -1) u * NX.tameVal (T.delta i) P (if b then 1 else -1) u') ∧
      ∀ u u' : 𝓞 D.host.E, u ∉ P.asIdeal → u - u' ∈ P.asIdeal →
        NX.tameVal (T.delta i) P (if b then 1 else -1) u = NX.tameVal (T.delta i) P (if b then 1 else -1) u') →
    ∃ (J : Subgroup (GAf D.host.E D.R.nV)) (χ : J →* (FractionRing (T.Ok i k))ˣ),
      (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong D.host.E D.R.nV N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) ∧
      NX.HypOutsideF J χ (badVT D T i Q) ∧
      (∀ κ : GAf D.host.E D.R.nV, κ ∈ J ↔ κ ∈ Umax D.host.E D.R.nV ∧
        (∀ kv, NX.InLevG (sp (NX.pG D kv)).v D.R.r (NX.locM (sp (NX.pG D kv)) κ)) ∧
        (∀ P ∈ QP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ)) ∧
        (∀ P ∈ DP, NX.InParah (sp P).v D.R.r (NX.locM (sp P) κ))) ∧
      ∀ κ (h : κ ∈ J), ((χ ⟨κ, h⟩ : (FractionRing (T.Ok i k))ˣ) : FractionRing (T.Ok i k)) =
        (∏ kv : (Σ kk : Fin 2, D.nd.PlG kk), gValT D T θ i k b kv (sp (NX.pG D kv)) (redG kv) (tauT D T i j b kv)
          (NX.locM (sp (NX.pG D kv)) κ)) *
        (∏ P ∈ QP, algebraMap (T.Ok i k) (FractionRing (T.Ok i k))
          (NX.tameVal ψ P 1 (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) *
        (∏ P ∈ DP, baseCoeffToExtFractionRing D T i k (NX.tameVal (T.delta i) P (if b then 1 else -1)
          (NX.resRep (sp P) P (NX.detT D.R.r (NX.locM (sp P) κ)))).1) := by
  first | exact @GlobalTheory.LevGChar.levGroup_exists | exact GlobalTheory.LevGChar.levGroup_exists | (intros; apply GlobalTheory.LevGChar.levGroup_exists <;> assumption)
