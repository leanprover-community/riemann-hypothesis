module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMeasurableRealOrbitMapOfAdelicOrbit
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices

@[expose] public section

open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct

theorem _root_.GlobalTheory.T.exists_measurable_realOrbitMap_of_adelicOrbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)), IsCMFam τ → ∀ (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ) (J : Matrix (Fin M) (Fin M) E) (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ) (N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ), (∀ ρ, N ρ * A ρ = 1) → (∀ ρ, A ρ * N ρ = 1) → ∀ x : Fin 1 → Fin M → E, AllSome (fun pt : (I → UpqT P Q) → (Fin 1 → Fin M → Ainf F ⊗[F] E) => ∀ g ρ, infCoord (θ ρ) (A ρ) (pt g) = UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) fun pt => Measurable pt ∧ (∀ g g', (∀ ρ, UpqT.mat (g ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i)) = UpqT.mat (g' ρ)⁻¹ *ᵥ (A ρ *ᵥ fun i => τ ρ (x 0 i))) → pt g = pt g') ∧ ∀ (h : HA (AF F) σ J) (t : I → UpqT P Q), (∀ ρ, UpqT.mat (t ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) → pt t = projInf (h⁻¹ • ratTup (F := F) (AF F) x) := by
  first | exact @GlobalTheory.RealOrbitMap.realOrbit | exact GlobalTheory.RealOrbitMap.realOrbit | (intros; apply GlobalTheory.RealOrbitMap.realOrbit <;> assumption)
