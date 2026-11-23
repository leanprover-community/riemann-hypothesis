module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePairingInjectiveEquivariantLevelMap
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tracePairing_injective_equivariant_levelMap : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL] (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (lam : LL →ₗ[ℚ_[l]] ℚ_[l]), (∀ a : LL, (∀ b : O, ∃ u : ℤ_[l], lam (a * algebraMap O LL b) = (u : ℚ_[l])) ↔ ∃ b : O, algebraMap O LL b = a) → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), (∀ g : ↥(GK K), ∃ u : ℤ_[l], (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (u : ℚ_[l]) ∧ (PadicInt.toZModPow r u : ZMod (l ^ r)) = ((Formalism.GaloisCohomology.cycK l K.1 r (IntermediateField.fixingSubgroupEquiv K.1 g) : (ZMod (l ^ r))ˣ) : ZMod (l ^ r))) → ∀ (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] (e : (↥LA.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) ≃+ M) (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K.1) M), (∀ g x, rho g (e x) = e (actQ LA _ hI ((IntermediateField.fixingSubgroupEquiv K.1).symm g) x)) → ∃ Ψ : (↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) →+ ReciprocityTheory.Gal.TDual (ZMod (l ^ r)) M, Function.Injective Ψ ∧ ∀ g y, Ψ (actQ LA' _ hI' ((IntermediateField.fixingSubgroupEquiv K.1).symm g) y) = ReciprocityTheory.Gal.twDual (Formalism.GaloisCohomology.cycK l K.1 r) rho g (Ψ y) := by
  first | exact @GlobalTheory.tracePairing_levelMap | exact GlobalTheory.tracePairing_levelMap | (intros; apply GlobalTheory.tracePairing_levelMap <;> assumption)
