module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAutomorphicFormFixedOfLocallyIntegralFixed
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

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix

theorem _root_.GlobalTheory.T.smoothAutomorphicForm_fixed_of_locally_integral_fixed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsAutForm φ → ∀ S : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ S, ∀ k ∈ KGL w (n := a), act (.fin (locGL E a w k)) φ = φ) → ∀ k : GL (Fin a) (Af E), (∀ w ∉ S, GeneralLinearGroup.map (pLoc E w) k ∈ KGL w (n := a)) → (∀ w ∈ S, GeneralLinearGroup.map (pLoc E w) k = 1) → act (.fin k) φ = φ := by
  first | exact @GlobalTheory.CuspRep.fixed_of_locFixed | exact GlobalTheory.CuspRep.fixed_of_locFixed | (intros; apply GlobalTheory.CuspRep.fixed_of_locFixed <;> assumption)
