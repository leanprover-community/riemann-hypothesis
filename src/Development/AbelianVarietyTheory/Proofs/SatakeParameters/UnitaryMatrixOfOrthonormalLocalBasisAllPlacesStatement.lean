module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryMatrixOfOrthonormalLocalBasisAllPlaces
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

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

theorem _root_.GlobalTheory.T.unitaryMatrix_of_orthonormal_localBasis_allPlaces : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ γ : Fin r → (OrbitPlaces.Pl D × Fin N × Fin N') → MaximalUnramifiedExtension p, (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) ∧ (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (thOrth D lam c b G) := by
  first | exact @GlobalTheory.KerStd.unitary_of_orthonormal | exact GlobalTheory.KerStd.unitary_of_orthonormal | (intros; apply GlobalTheory.KerStd.unitary_of_orthonormal <;> assumption)
