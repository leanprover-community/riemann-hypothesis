module

public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamExistsHodgeTateEigenbasis
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.deRham_exists_hodgeTate_eigenbasis : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (m : ℕ) (r' : ↥(GK K) →* Matrix.GeneralLinearGroup (Fin m) ↥LL.1), let ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1) := ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL.1 ≃ₐ[↥LL.1] _) : _ →* _).comp ((Units.coeHom _).comp r'); Module.finrank ↥LL.1 ↥(DdR (P.PD K) ρ) = Module.finrank ℚ_[l] ↥K.1 * m → (∀ (σ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), σ x ∈ LL.1) → ∀ τ' : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, (∀ x : ↥K.1, ((τ' x : ↥LL.1) : Om l) = (x : Om l)) → ∀ (K' : FinExt l), K.1 ≤ K'.1 → LL.1 ≤ K'.1 → ∃ (Pm : Matrix.GeneralLinearGroup (Fin m) ℂ_[l]) (k : Fin m → ℤ), (∀ a : ℤ, ((Multiset.map k Finset.univ.val).count a : ℤ) = multV (P.PD K) ρ τ' a) ∧ ∀ g : ↥(GK K), (g : GQ l) ∈ GK K' → (r' g : Matrix (Fin m) (Fin m) ↥LL.1).map (fun x => (((x : ↥LL.1) : Om l) : ℂ_[l])) * (Pm : Matrix (Fin m) (Fin m) ℂ_[l]).map (Per.σC (g : GQ l)) = (Pm : Matrix (Fin m) (Fin m) ℂ_[l]) * Matrix.diagonal (fun i => ((((P.χQ (g : GQ l)) ^ (-k i) : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l])) := by
  first | (exact @GlobalTheory.HTBasis.htc_basis) | (exact GlobalTheory.HTBasis.htc_basis) | (intros; apply GlobalTheory.HTBasis.htc_basis  <;> assumption)
