module

public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialFrameMapsBounded
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_polynomial_frame_maps_bounded : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), (∀ k, k + 1 < D.R.m → R.ItY k ≠ 0) → R.ItX ≠ 0 → ∃ (d : ∀ j, (R.MY j).Vec) (dX : R.MX.Vec) (φ : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank) (φX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank), (∀ j, j < D.R.m → ∀ τ, ‖(d j τ : (R.MY j).H τ)‖ = 1) ∧ (∀ τ, ‖(dX τ : R.MX.H τ)‖ = 1) ∧ (∀ k, k + 1 < D.R.m → ellT (R.MY k) (fun τ => (d k τ : (R.MY k).H τ)) (inclT (R.MY k) (R.ItY k (φ k) (PiTensorProduct.tprod ℂ (d (k + 1))))) = 1) ∧ ellT (R.MY (D.R.m - 1)) (fun τ => (d (D.R.m - 1) τ : (R.MY (D.R.m - 1)).H τ)) (inclT (R.MY (D.R.m - 1)) (R.ItX φX (PiTensorProduct.tprod ℂ dX))) = 1 := by
  first | exact @GlobalTheory.Mem.UnitPairing.exists_unit_vectors | exact GlobalTheory.Mem.UnitPairing.exists_unit_vectors | (intros; apply GlobalTheory.Mem.UnitPairing.exists_unit_vectors <;> assumption)
