module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat
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

@[expose] public section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn

theorem _root_.GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.VacBridge.exists_bridge | exact GlobalTheory.VacBridge.exists_bridge | (intros; apply GlobalTheory.VacBridge.exists_bridge <;> assumption)
