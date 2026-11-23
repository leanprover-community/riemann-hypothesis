module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCentralizerStabilizerEqLatticeStabilizer
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

theorem _root_.GlobalTheory.T.relIndex_centralizerStabilizer_eq_latticeStabilizer : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  first | exact @GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | exact GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat | (intros; apply GlobalTheory.OrbWeights.relIndex_stab_eq_relIndex_stabLat <;> assumption)
