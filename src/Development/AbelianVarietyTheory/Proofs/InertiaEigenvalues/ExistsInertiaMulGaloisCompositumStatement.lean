module

public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInertiaMulGaloisCompositum
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
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CrystallineSubrepresentation
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RealisesUnitPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

theorem _root_.GlobalTheory.T.exists_inertia_mul_galois_compositum : ∀ (l : ℕ) [Fact l.Prime] (K' F K'' : FinExt l), (GK K').Normal → K''.1 = K'.1 ⊔ F.1 → ∀ h : GQ l, h ∈ GK F → (∀ x ∈ K0 K'', h x = x) → ∃ i : ↥(GK (Formalism.MainNotions.ElementDenominator.qlExt l)), i ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (i : GQ l) ∈ GK F ∧ (i : GQ l)⁻¹ * h ∈ GK K'' := by
  first | exact @GlobalTheory.InertiaLift.lift | exact GlobalTheory.InertiaLift.lift | (intros; apply GlobalTheory.InertiaLift.lift <;> assumption)
