module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowSmulLatticeOfCoordDvd
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.mem_pow_smul_lattice_of_coord_dvd : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) → ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y := by
  first | exact @GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd | exact GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd | (intros; apply GlobalTheory.InertiaEigenvalues.mem_pow_smul_of_coord_dvd <;> assumption)
