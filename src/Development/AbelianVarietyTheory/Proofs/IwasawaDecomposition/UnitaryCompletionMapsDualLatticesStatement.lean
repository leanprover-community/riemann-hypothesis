module

public import Formalism.LocalToGlobal.HermitianForms.PrkSmul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryCompletionMapsDualLattices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply

@[expose] public section

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

theorem _root_.GlobalTheory.T.unitary_completion_maps_dualLattices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E)) (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)), IsUnit J.det → Submodule.IsFullLattice E L → Submodule.IsFullLattice E Lb → y ∈ UPts σ J (v.adicCompletion F) → (∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) → ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔ (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  first | exact @GlobalTheory.DualCompletion.dual_move | exact GlobalTheory.DualCompletion.dual_move | (intros; apply GlobalTheory.DualCompletion.dual_move <;> assumption)
