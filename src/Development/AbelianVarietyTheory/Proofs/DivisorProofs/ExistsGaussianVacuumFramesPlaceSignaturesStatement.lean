module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignatures
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

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.HoweD.exists_vacuumD | exact GlobalTheory.HoweD.exists_vacuumD | (intros; apply GlobalTheory.HoweD.exists_vacuumD <;> assumption)
