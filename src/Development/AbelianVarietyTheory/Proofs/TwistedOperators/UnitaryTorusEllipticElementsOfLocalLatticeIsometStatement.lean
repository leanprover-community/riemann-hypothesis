module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEllipticElementsOfLocalLatticeIsomet
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.unitaryTorusEllipticElements_of_localLatticeIsometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n n' : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E) (L : Submodule (𝓞 E) (Fin n → E)) (L' : Submodule (𝓞 E) (Fin n' → E)) (v : HeightOneSpectrum (𝓞 F)) (j : GLoc σ J v ≃ₜ* GLoc σ J' v), IsLatticeConj L L' j → XSet P (Fv F v) J' = XSet P (Fv F v) J ∧ ∀ (x : plusUnits P (Fv F v)) (φ : ((Fv F v) ⊗[F] Fld P) ≃ₗ[(Fv F v) ⊗[F] E] (Fin n → (Fv F v) ⊗[F] E)) (h : IsIsom P (Fv F v) J x.1.1 φ), ∃ (φ' : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n' → Fv F v ⊗[F] E)) (h' : IsIsom P (Fv F v) J' x.1.1 φ'), gam h' = j (gam h) ∧ ∀ t, torEmb h' t = j (torEmb h t) := by
  first | exact @GlobalTheory.trEll_latticeConj_move | exact GlobalTheory.trEll_latticeConj_move | (intros; apply GlobalTheory.trEll_latticeConj_move <;> assumption)
