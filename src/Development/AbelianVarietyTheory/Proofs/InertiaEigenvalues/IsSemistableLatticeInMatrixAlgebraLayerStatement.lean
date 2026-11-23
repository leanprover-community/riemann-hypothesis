module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemistableLatticeInMatrixAlgebraLayer
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isSemistable_latticeInMatrixAlgebraLayer : ∀ (l : ℕ) [Fact l.Prime] (K L₀ : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (a : ℕ) (Cl : Set (↥(GK K) →* GL (Fin a) (Om l))) (d : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (Ly : Layer L₀ Cl ρ), ((∀ ρ₁ ∈ Cl, ∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsSst P R) → IsSst P (qRep ρ)) ∧ ((∀ ρ₁ ∈ Cl, (∀ (L : FinExt l) (r' : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), L₀.1 ≤ L.1 → (∀ g v, R g v = (r' g).val *ᵥ v) → (∀ g i j, (((r' g).val i j : ↥L.1) : Om l) = (ρ₁ g).val i j) → IsCrys (P.PD K) R)) → IsCrys (P.PD K) (qRep ρ)) := by
  first | exact @GlobalTheory.LayerSst.main | exact GlobalTheory.LayerSst.main | (intros; apply GlobalTheory.LayerSst.main <;> assumption)
