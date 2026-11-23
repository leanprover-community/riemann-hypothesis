module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RhoIsCoc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFiniteGenerationOfAffineBaseChange
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

theorem _root_.GlobalTheory.T.cech_finite_generation_of_affine_base_change : ∀ (G X : Scheme.{0}) (p : G ⟶ X) (U : X.affineOpens) (J : Type) (W : J → G.Opens) (hWU : ∀ i, W i ≤ p ⁻¹ᵁ U.1), CechFG (fun i => pullback.fst p U.2.fromSpec ⁻¹ᵁ W i) Γ(X, U.1) (fun i i' => (secMap (R := Γ(X, U.1)) (pullback.snd p U.2.fromSpec) _).hom) → CechFG W Γ(X, U.1) (fun i i' => (p.appLE U.1 (W i ⊓ W i') (inf_le_left.trans (hWU i))).hom) := by
  first | exact @GlobalTheory.CechTr.cechFG_of_baseChange_affine | exact GlobalTheory.CechTr.cechFG_of_baseChange_affine | (intros; apply GlobalTheory.CechTr.cechFG_of_baseChange_affine <;> assumption)
