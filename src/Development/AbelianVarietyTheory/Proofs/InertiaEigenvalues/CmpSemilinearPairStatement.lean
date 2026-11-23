module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CmpSemilinearPair
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.cmp_semilinear_pair_alt : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T), IsCrisCmp I jB → ∀ (μ : OA l O), IsUnit (toB l O μ) → (∀ v ∈ LA t ϖ P, ∃ z : TW (OA l O) T, I.j (inclO l O μ • v) = TWincl (inclO l O) T z) → ∀ (σA : OA l O →ₐ[O] OA l O) (σW : OW l O →ₐ[O] OW l O) (σB : OB l O →ₐ[O] OB l O) (h : ↥T.L.T →ₗ[O] ↥T.L.T) (F : (ι → OW l O) →ₗ[O] (ι → OW l O)) (lam : OA l O) (Γ : Matrix ι ι (OA l O)), (∀ x, inclO l O (σA x) = σW (inclO l O x)) → (∀ x, toB l O (σA x) = σB (toB l O x)) → (∀ v, I.j (F v) = TensorProduct.map σW.toLinearMap h (I.j v)) → (∀ (r : OW l O) v, F (r • v) = σW r • F v) → (∀ c, inclO l O lam • F (inclL t ϖ P c) = inclL t ϖ P (Γ *ᵥ fun i => σA (c i))) → ∀ v : ι → OB l O, jB (Γ.map (toB l O) *ᵥ fun i => σB (v i)) = toB l O lam • TensorProduct.map σB.toLinearMap h (jB v) := by
  first | exact @GlobalTheory.BKGal.cmp_semilinear_pair | exact GlobalTheory.BKGal.cmp_semilinear_pair | (intros; apply GlobalTheory.BKGal.cmp_semilinear_pair <;> assumption)
