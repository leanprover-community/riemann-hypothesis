module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesPair
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

theorem _root_.GlobalTheory.T.greenbergWiles_pair_alt : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (G F Ω) W) (ρ' : Representation Λ (G F Ω) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (A : Formalism.GaloisCohomology.Places F Ω), ContainsAbove S l → (∀ v ∉ S, ∀ B : ValuationSubring Ω, IsPlaceOver B v → ∀ τ ∈ Ine (F := F) B, ρ τ = 1 ∧ ρ' τ = 1) → ∀ (L : ∀ v, Submodule Λ (H1 (ρ.comp (Dec (F := F) (A.1 v)).subtype))), (∀ v ∉ S, L v = Formalism.GaloisCohomology.unrAt ρ (A.1 v)) → ∀ C : Set (H1 ρ'), (∀ y : Z1 ρ', Submodule.Quotient.mk y ∈ C ↔ (∀ v ∉ S, ∀ τ ∈ Ine (F := F) (A.1 v), y.1 τ = 0) ∧ ∀ v ∈ S, ∀ x : Z1 (ρ.comp (Dec (F := F) (A.1 v)).subtype), Submodule.Quotient.mk x ∈ L v → CupB (fun g : Dec (F := F) (A.1 v) => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g.1 m) P x.1 (fun g => y.1 g.1)) → Finite C ∧ Nat.card (Formalism.GaloisCohomology.SelAll ρ A L) * Nat.card (H0 ρ') * (∏ v ∈ S, Nat.card (H0 (ρ.comp (Dec (F := F) (A.1 v)).subtype))) * Nat.card W ^ InfinitePlace.nrComplexPlaces F = Nat.card C * Nat.card (H0 ρ) * ∏ v ∈ S, Nat.card (L v) := by
  first | exact @GlobalTheory.PairFormula.greenbergWiles_pair | exact GlobalTheory.PairFormula.greenbergWiles_pair | (intros; apply GlobalTheory.PairFormula.greenbergWiles_pair <;> assumption)
