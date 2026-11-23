module

public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.GraphHeightLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoublingNormDetInertPlaceLatticeLength
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

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.GraphHeightLattice
open Formalism.UG (GLint)

theorem _root_.GlobalTheory.T.doublingNorm_det_inertPlace_lattice_length : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsFullLattice E L] (v : HeightOneSpectrum (𝓞 F)), ∀ P : HeightOneSpectrum (𝓞 E), IsInertUnder v P → ∀ (g : GLoc σ J v) (α : GL (Fin n) (Fv F v ⊗[F] E)), (∀ y : Fin n → Fv F v ⊗[F] E, (y ∈ latLoc F L v ∧ y ∈ latMoved σ J L v g) ↔ ∃ x ∈ latLoc F L v, y = α.1 *ᵥ x) → ∃ l : ℕ, latLength σ J L v g = l ∧ absEv F E v (Matrix.GeneralLinearGroup.det α) = ((Ideal.absNorm P.asIdeal : ℕ) : ℝ≥0) ^ (-(l : ℤ)) := by
  first | exact @GlobalTheory.InertLatLength.absEv_det_eq_of_inert | exact GlobalTheory.InertLatLength.absEv_det_eq_of_inert | (intros; apply GlobalTheory.InertLatLength.absEv_det_eq_of_inert <;> assumption)
