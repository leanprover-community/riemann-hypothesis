module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Formalism.LocalToGlobal.IndefiniteReal.FWTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisConjCoverFunctionEqConstMulConjTuple
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

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

theorem _root_.GlobalTheory.T.galoisConj_coverFunction_eq_const_mul_conjTuple : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∃ k0 : ℂ, IsRoot1 k0 ∧ ∀ (a b : Tp) (cx : Rul (M.dδ a).Xo₂ (M.dδ a).c₂), M.dδ b = { M.dδ a with cδ := cx } → HEq (M.U₂ b) (M.U₂ a) → HEq (M.dict₂ b) (M.dict₂ a) → ConjTup R τ (tup a) (tup b) → ∃ (h₂ : Fixes (M.dδ a).c₂ (covAut (M.dδ a) ta)) (ka : M.c'.F) (s : (AE D)ˣ), (ka : ℂ) = k0 * ((R.xi (tup b) s : Circle) : ℂ) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra (M.dδ a).c₂.F k] (y₂ : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ k), evR (M.dδ a).Xo₂ (M.dδ a).c₂ (galRul h₂ (M.dδ a).cδ) y₂ = algebraMap (M.dδ a).c₂.F k ((M.dδ a).eF ka) * evR (M.dδ a).Xo₂ (M.dδ a).c₂ cx y₂ := by
  first | exact @GlobalTheory.CoverConj.conj_cover_const | exact GlobalTheory.CoverConj.conj_cover_const | (intros; apply GlobalTheory.CoverConj.conj_cover_const <;> assumption)
