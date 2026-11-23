module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinorProductPairingDeterminedByCanonicalMap
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.minorProductPairing_determined_by_canonicalMap : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1) (nu : Bool × HH D → YoungDiagram)
    (hnu : ∀ z, (nu z).colLen 0 ≤ N0) (Th : MvPowerSeries ((Bool × HH D) × Fin N0 × Fin N1) ℂ_[p])
    (ph : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N0) ℂ_[p]))
    (ph' : Module.Dual ℂ_[p] (MvPolynomial ((Bool × HH D) × ℕ × Fin N1) ℂ_[p]))
    (κ : ℂ_[p]) (Q : MvPolynomial ((Bool × HH D) × Fin N0 × ℕ) ℂ_[p])
    (hQ : ∀ y : Bool × HH D → Fin N0 → ℕ → ℂ_[p], MvPolynomial.eval (fun v => y v.1 v.2.1 v.2.2) Q = ph (GL3Columns.DeX N0 nu y))
    (h : ∀ y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p],
      ph' (GL3Columns.DeX N1 nu fun s => GL3Columns.colsOf (y' (tauPl D s))) = κ * GL3Columns.applyQ p N0 N1 Th Q (fun s => GL3Columns.colsOf (y' (tauPl D s))))
    (I : KM.ColChoice N1 nu), ph' (MvPolynomial.map (Int.castRingHom _) (KM.nablaX N1 nu I)) = κ * ph (KM.applyAt0 N0 N1 p Th (KM.Gxz N0 N1 nu I)) := by
  first | exact @GlobalTheory.KForm.WWUnique.ww_unique | exact GlobalTheory.KForm.WWUnique.ww_unique | (intros; apply GlobalTheory.KForm.WWUnique.ww_unique <;> assumption)
