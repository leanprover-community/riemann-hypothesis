module

public import Mathlib.RingTheory.IsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtension
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


theorem _root_.GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension : ∀ (S A EE O W RW D Y : Type) [CommRing S] [CommRing A] [CommRing EE] [CommRing O] [CommRing W] [CommRing RW] [Algebra O A] [Algebra A EE] [Algebra O EE] [IsScalarTower O A EE] [Algebra O RW] [AddCommGroup D] [Module EE D] [Module A D] [IsScalarTower A EE D] [AddCommGroup Y] [Module RW Y] (a : S →+* A) (ι : EE →ₐ[O] RW) (c : W →+* RW) (jD : D →+ Y), Function.Injective ι → (∀ e, IsUnit (ι e) → IsUnit e) → (∀ (e : EE) (x : D), jD (e • x) = ι e • jD x) → (∀ s, ι (algebraMap A EE (a s)) ∈ Set.range c) → ∀ (d r : ℕ) (o : Fin d → O), (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j) → Nonempty (Module.Basis (Fin r) EE D) → ∀ (q : ℕ) (x : Fin q → D), q = d * r → (∀ y : Y, ∃! w : Fin q → W, y = ∑ i, c (w i) • jD (x i)) → ∀ N : Submodule A D, (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → IsBaseChange EE N.subtype := by
  first | exact @GlobalTheory.isBaseChange_subtype_of_basis_after_extension | exact GlobalTheory.isBaseChange_subtype_of_basis_after_extension | (intros; apply GlobalTheory.isBaseChange_subtype_of_basis_after_extension <;> assumption)
