module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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


theorem _root_.GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  first | exact @GlobalTheory.prod_aeval_aroots_padic_eq_det | exact GlobalTheory.prod_aeval_aroots_padic_eq_det | (intros; apply GlobalTheory.prod_aeval_aroots_padic_eq_det <;> assumption)
