module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
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

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod

theorem _root_.GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) , (∀ (S : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y), (∀ gk : GL Y k, ∃! g, p.IsLoc F g gk) ∧ (∀ g, SuppAt p.e S g → ∃ gk, p.IsLoc F g gk) ∧ ∀ g gk h hk, p.IsLoc F g gk → p.IsLoc F h hk → p.IsLoc F (g * h) (gk * hk)) ∧ (∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (J : JacLev D ρ) (s hh : k) (F₀ : Frame k J.W₀.rank n) (F : Frame k J.W.rank (n ⊕ Fin c)), p.IsJacFrame J s hh F₀ F → ∀ g β q, q ∈ R k n c (ρ + 1) → p.IsLoc F g (colE c (ρ + 1) β * q) → g ∈ jacGrp J.d) ∧ ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) (B : BesLev D ρ) (s : k) (FA : Frame k B.A.rank n) (F : Frame k B.V.rank (n ⊕ Fin c)), p.IsBesFrame B s FA F → ∀ g q, q ∈ R k n c (ρ + 1) → p.IsLoc F g q → g ∈ besGrp B.d B.o := by
  first | exact @GlobalTheory.LocGrp.local_groups | exact GlobalTheory.LocGrp.local_groups | (intros; apply GlobalTheory.LocGrp.local_groups <;> assumption)
