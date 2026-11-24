module

public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetMapFrameEqApplyQAdaptedCoordinates
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
open Classical

theorem _root_.GlobalTheory.T.jetMap_frame_eq_applyQ_adapted_coordinates : ∀ (D : D7) {p : ℕ} [Fact p.Prime] (N0 N1 : ℕ) (hN : N0 ≤ N1)
    (T : MvPowerSeries (D.what₂.Tau × Fin N1 × Fin N0) ℂ_[p]) (s : D.what₂.Tau → ℂ_[p])
    (B : D.what₂.Tau → Matrix (Fin N0) (Fin N0) ℂ_[p]) (B' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p])
    (hB : ∀ τ, (B τ).det ≠ 0) (P : MvPolynomial (GL3Theta.FrV D N0) ℂ_[p]) (y' : D.what₂.Tau → Matrix (Fin N1) (Fin N1) ℂ_[p]), MvPolynomial.eval (fun k : GL3Theta.FrV D N1 => (B' k.1 * y' k.1) k.2.1 k.2.2)
      (jetMap (fun m => (m.prod fun k n => s k.1 ^ n) * (m.prod fun _ n => (n.factorial : ℂ_[p])) * MvPowerSeries.coeff m T)
        (fun _ => 0) P) =
    GL3Columns.applyQ p N0 N1
      (atLin (fun (k : D.what₂.Tau × Fin N1 × Fin N0) (j : (Bool × HH D) × Fin N0 × Fin N1) =>
          if tauPl D j.1 = k.1 then 1 * s k.1 * B' k.1 k.2.1 j.2.2 * (B k.1)⁻¹ j.2.1 k.2.2 else 0)
        (fun j => MvPowerSeries.X j) T)
      (MvPolynomial.aeval (fun k : GL3Theta.FrV D N0 => ∑ a : Fin N0,
          MvPolynomial.C (B k.1 k.2.1 a) * MvPolynomial.X ((Equiv.ofBijective (tauPl D) (tauPl_bij D)).symm k.1, a, (k.2.2 : ℕ))) P)
      (fun z => GL3Columns.colsOf (y' (tauPl D z))) := by
  first | exact @GlobalTheory.JetChain.jetMap_frame_eq_applyQ | exact GlobalTheory.JetChain.jetMap_frame_eq_applyQ | (intros; apply GlobalTheory.JetChain.jetMap_frame_eq_applyQ <;> assumption)
