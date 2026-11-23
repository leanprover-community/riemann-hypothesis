module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DescentFreeModuleCocycle
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAdicCompleteOfPowLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemBallOfGaugeLt
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.descent_free_module_cocycle : ∀ (A B D T : Type) [CommRing A] [CommRing B] [CommRing D] [CommRing T] [Algebra A B] (p q : B →+* D) (q₁₂ q₂₃ q₁₃ : D →+* T) (q₃ : B →+* T), (algebraMap A B).FaithfullyFlat → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom p) (CommRingCat.ofHom q) → CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom (p.comp (algebraMap A B))) (CommRingCat.ofHom q₃) (CommRingCat.ofHom q₁₂) → q₂₃.comp p = q₁₂.comp q → q₂₃.comp q = q₃ → q₁₃.comp p = q₁₂.comp p → q₁₃.comp q = q₃ → ∀ (d : ℕ) (ε : Matrix (Fin d) (Fin d) D), IsUnit ε → ε.map q₁₂ * ε.map q₂₃ = ε.map q₁₃ → ∀ N : Submodule A (Fin d → B), (∀ z, z ∈ N ↔ (fun i => p (z i)) = ε.mulVec fun i => q (z i)) → Module.Finite A ↥N ∧ Module.Projective A ↥N ∧ IsBaseChange B N.subtype := by
  first | exact @GlobalTheory.descent_free_cocycle | exact GlobalTheory.descent_free_cocycle | (intros; apply GlobalTheory.descent_free_cocycle <;> assumption)
