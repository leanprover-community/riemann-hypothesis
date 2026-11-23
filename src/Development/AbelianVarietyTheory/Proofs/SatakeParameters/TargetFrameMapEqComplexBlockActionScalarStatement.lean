module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivFrameBTheta
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RkLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TargetFrameMapEqComplexBlockActionScalar
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

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelProjection Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwV.DelA
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.targetFrameMap_eq_complexBlockAction_scalar : ∀ {p : ℕ} [Fact p.Prime] (X : Sys p) (D : D7) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (Kc : Type) [Field Kc] [Algebra (Formalism.MainNotions.FormalGroupSystem.K0 p) Kc] [Algebra X.G.Kf Kc] (ι : ℂ →+* Kc) (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), PosTie X D pos Kc ι ρ → ∀ (fd : FData X D) (c : Kc), c ≠ 0 → ∀ (j : ℕ) (hN : RankTie X D j) (La' : X.Lt (j + 1)) (M : GL (Fin (D.R.N (j + 1))) D.host.E), StdU D M → FrIs fd ρ (j + 1) La' (rkT X D hN) M → ∀ (ν : D.what₂.Tau → Fin (D.R.N j) → ℕ), NuIs X D pos j ν → ∀ P : MvPolynomial (GL3Theta.FrV D (D.R.N (j + 1))) ℂ, P ∈ WtPol ℂ (extNu (D.R.N (j + 1)) ν) → GlobalTheory.FrameB.tauV Kc fd c j La' (phi0 X D pos ι j P) = (c ^ (∑ τ, szT X D pos j τ) * ι (∏ τ, embT D τ M.1.det ^ wT X D pos j τ)) • MvPolynomial.map ι (actC X D pos (j + 1) (rkT X D hN) M⁻¹ (phiC X D pos (j + 1) (rkT X D hN) (wT X D pos j) P)) := by
  first | exact @GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | exact GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt | (intros; apply GlobalTheory.TwV.DelA.targetFrameMap_eq_complexBlockAction_scalar_alt <;> assumption)
