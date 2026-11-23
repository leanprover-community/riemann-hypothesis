module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceClassMatchingCouplingCoset
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalCondMoveDecoratedLattice

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_reference_class_matching_coupling_coset : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ (c : (I.stp u a i).Cl) (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i), ∃ c0 : (I.stp u I.mu0 i).Cl, c0.1 = b0 ∧
      ∃ y : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), y ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp ∧
      ∀ (κ : (I.stp u a i).G c.1) (κ0 : (I.stp u I.mu0 i).G c0.1), (I.stp u a i).gam c.1 κ = 1 → (I.stp u I.mu0 i).gam c0.1 κ0 = 1 →
        κ.2.2 = 1 → (i + 1 = B.R.m → ∀ w, κ0.2.1.1 w = y w * κ.2.1.1 w * (y w)⁻¹) →
        (cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
          cosetIn ((I.stp u I.mu0 i).act c0.1 κ0 ((I.stp u I.mu0 i).rep c0)) = cosetIn ((I.stp u I.mu0 i).rep c0)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match <;> assumption)
