module

public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TatePairingLatticeLevelPrimePow
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

theorem _root_.GlobalTheory.T.tate_pairing_lattice_level_primePow : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA.T)) (hI' : StableSub LA' (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)), ∃ β : QuotientCohomology LA' _ hI' →ₗ[O] QuotientCohomology LA _ hI →ₗ[O] (LL ⧸ LinearMap.range (Algebra.linearMap O LL)), (∀ c, (∀ y, β y c = 0) → c = 0) ∧ ∀ (d : ↥(latticeCocycles LA)) (h : redT LA _ d ∈ quotientCocycles LA _ hI) (c' : ↥(quotientCocycles LA' _ hI')), β (Submodule.Quotient.mk c') (Submodule.Quotient.mk ⟨redT LA _ d, h⟩) = 0 → CobO (P.PD K) L1 (cupLD LA' m (d : ↥(GK K) → A.V) (fun g => (Submodule.Quotient.mk ((((l : ℕ) : LL) ^ r)⁻¹ • Formalism.MainNotions.LocalSituation.liftQ LA' _ ((c' : ↥(GK K) → ↥LA'.T ⧸ (Ideal.span {((l : ℕ) : O) ^ r} • ⊤ : Submodule O ↥LA'.T)) g)) : A'.V ⧸ LA'.T))) := by
  first | exact @GlobalTheory.TateLevel.tate_pairing_level | exact GlobalTheory.TateLevel.tate_pairing_level | (intros; apply GlobalTheory.TateLevel.tate_pairing_level <;> assumption)
